package com.kcsl.loops;


import java.awt.Color;
import java.io.File;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;

import com.ensoftcorp.atlas.core.db.graph.Edge;
import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasHashSet;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.index.common.SourceCorrespondence;
import com.ensoftcorp.atlas.core.markup.Markup;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.DisplayUtil;
import com.ensoftcorp.atlas.ui.viewer.graph.SaveUtil;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.kcsl.loops.VerificationProperties;
import com.ensoftcorp.atlas.core.markup.Markup;
import com.ensoftcorp.atlas.core.markup.MarkupProperty;

import com.kcsl.loops.log.Log;

/**
* This program checks if a given function or all functions in mapped workspace are structured
* It parses through all the control flow condition nodes and obtain the subgraph under them
* If the subgraph has more than one entries, it is unstructured.
*
* @author Le Zhang
*/
public class loopAnalyzer {
	
	/**
	 * The name pattern for the directory containing the graphs for the processed goto.
	 * <p>
	 * 1- The {@link SourceCorrespondence}.
	 */
	private static final String GOTO_GRAPH_DIRECTORY_NAME_PATTERN = "gotoCycle_graphs";
	
	/**
	 * The directory where the verification graphs for the processed lock to be stored}.
	 */
	private static File currentgotoGraphsOutputDirectory;
	
	/**
	 * The root output directory for all the graphs. The current class with create a directory with {@link #currentLockGraphsOutputDirectory}
	 * to store all generated graph per processed lock.
	 */
	private Path graphsOutputDirectory;
	
	/**
	 * The name pattern for the CFG graph.
	 * <p>
	 * The following is the parts of the name:
	 * 1- The method name corresponding to the CFG.
	 */
	private static final String CFG_GRAPH_FILE_NAME_PATTERN = "PCG@%s@%s@%s";
	
	public loopAnalyzer()
	{
		this.graphsOutputDirectory = VerificationProperties.getGraphsOutputDirectory();
		
	}
	
	private static void saveDisplayCFG(Graph cfgGraph, String sourceFile, String methodName, Markup markup, boolean displayGraphs) { 
        if(displayGraphs){
            DisplayUtil.displayGraph(markup, cfgGraph);
        }
            
        try{
            String cfgFileName = String.format(CFG_GRAPH_FILE_NAME_PATTERN, sourceFile,methodName, VerificationProperties.getGraphImageFileNameExtension());
            SaveUtil.saveGraph(new File(currentgotoGraphsOutputDirectory, cfgFileName), cfgGraph, markup).join();
        } catch (InterruptedException e) {}
            
    }	
	
	private void createDirectory(){
        String containingDirectoryName = String.format(GOTO_GRAPH_DIRECTORY_NAME_PATTERN);
        currentgotoGraphsOutputDirectory = this.graphsOutputDirectory.resolve(containingDirectoryName).toFile();
        if(!currentgotoGraphsOutputDirectory.exists())
        {
        if(!currentgotoGraphsOutputDirectory.mkdirs()){
            Log.info("Cannot create directory:" + currentgotoGraphsOutputDirectory.getAbsolutePath());
        }
        }
    }
	
	private static Node getDeclarativeParent(Node node) {
		AtlasSet<Node> parentNodes = Common.toQ(node).parent().eval().nodes();
		if(parentNodes.size() > 1){
			throw new IllegalArgumentException("Multiple declarative parents!");
		}
		return parentNodes.one();
	}
	
	public static String getQualifiedName(Node node, String...stopAfterTags) {
		if(node == null){
			throw new IllegalArgumentException("Node is null!");
		}
		String result = node.attr().get(XCSG.name).toString();
		Node parent = getDeclarativeParent(node);
		boolean qualified = false;
		while (parent != null && !qualified) {
			for(String stopAfterTag : stopAfterTags){
				if(parent.taggedWith(stopAfterTag)){
					qualified = true;
				}
			}
			String prefix = parent.attr().get(XCSG.name).toString();
			if(!prefix.equals("")){
				result = parent.attr().get(XCSG.name) + "." + result;
			}
			parent = getDeclarativeParent(parent);
		}
		return result;
	}
	
	public static String getQualifiedFunctionName(Node function) {
		if(function == null){
			throw new IllegalArgumentException("Function is null!");
		}
		if(!function.taggedWith(XCSG.Function)){
			throw new IllegalArgumentException("Function parameter is not a function!");
		}
		return getQualifiedName(function, XCSG.Package);
	}
	
	public static void analyzeLoops() {
		// get saving directory
		new loopAnalyzer().createDirectory();
		
		// run DLI to tag all loops
		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
		
		// get all loop entry nodes
		Q all_loop_entry_nodes = Common.universe().nodesTaggedWithAny(XCSG.Loop);
		
		// get all functions that have loops
//		Q functions = all_loop_entry_nodes.containers().nodes(XCSG.Function);
//		AtlasSet<Node> function_set = functions.eval().nodes();

		// get all GOTO loop entry nodes (entry nodes should always be the label node)
		Q goto_loop_entry_nodes = CommonQueries.nodesStartingWith(all_loop_entry_nodes, "label ");

		// get all functions have GOTO loops
		AtlasSet<Node> function_goto_loop_set = goto_loop_entry_nodes.containers().nodes(XCSG.Function).eval().nodes();
		
		// output graph
		for(Node function : function_goto_loop_set) {
			// get CFG of this function
			Q cfg = CommonQueries.cfg(Common.toQ(function));
			
			// avoid empty CFGs
			if(!CommonQueries.isEmpty(cfg)) {
				// get loop label nodes
				AtlasSet<Node> loop_label_nodeset = CommonQueries.nodesStartingWith(cfg.nodes(XCSG.Loop), "label ").eval().nodes();
				
				// verify if the goto and label are the causes of the loop
				AtlasSet<Node> valid_loop_label_nodeset = new AtlasHashSet<Node>();
				for(Node loop_label : loop_label_nodeset) {
					AtlasSet<Node> loop_label_pred_goto = CommonQueries.nodesStartingWith(cfg.predecessors(Common.toQ(loop_label)), "goto ").eval().nodes();
					if(loop_label_pred_goto.size()==0) {
						continue;
					}
					AtlasSet<Node> loop_label_loopchild_goto = CommonQueries.nodesStartingWith(Common.universe().edges(XCSG.LoopChild).
							forward(Common.toQ(loop_label)).retainNodes(), "goto ").eval().nodes();
					if(loop_label_loopchild_goto.size()==0) {
						continue;
					}
					
					for(Node goto_node : loop_label_pred_goto) {
						if(loop_label_loopchild_goto.contains(goto_node)) {
							valid_loop_label_nodeset.add(loop_label);
							break;
						}
					}
				}
				
				// check if there are valid loop labels
				if(valid_loop_label_nodeset.size() == 0) {
					continue;
				}
				
				// if we have valid loop labels
				// get loop children nodes
				Q loop_children_nodes = Common.universe().edges(XCSG.LoopChild).forward(Common.toQ(valid_loop_label_nodeset)).retainNodes();
				
				
				// mark up
				Markup markup = new Markup();
				markup.set(loop_children_nodes, MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW);
				markup.set(Common.toQ(valid_loop_label_nodeset), MarkupProperty.NODE_BACKGROUND_COLOR, Color.RED);
				String sourceFile = getQualifiedFunctionName(function);
				String methodName =  function.getAttr(XCSG.name).toString();
				saveDisplayCFG(cfg.eval(),sourceFile,methodName, markup, false );
				
			}
			
			Log.info(function.getAttr(XCSG.name).toString());
		}
		
//		Log.info("=======================");
//		Log.info("Total loops: " + all_loop_entry_nodes.eval().nodes().size());
//		Log.info("Total Functions have loops: " + function_set.size());
//		Log.info("=======================");
//		
//		Log.info("Total Loops Formed by GOTO: " + loopCnt);
//		Log.info("Total Functions have GOTO loops: " + function_goto_loop_set.size());
//		Log.info("=======================");
//		
	}
	
}
