package com.kcsl.loops;


import java.awt.Color;
import java.io.File;
import java.nio.file.Path;


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
import com.ensoftcorp.open.pcg.common.PCGFactory;
import com.ensoftcorp.atlas.core.script.CommonQueries;
import com.kcsl.loops.VerificationProperties;
import com.ensoftcorp.atlas.core.markup.MarkupProperty;

import com.kcsl.loops.log.Log;

/**
* This program checks if a given function or all functions in mapped workspace are structured
* It parses through all the control flow condition nodes and obtain the subgraph under them
* If the subgraph has more than one entries, it is unstructured.
*
* @author Le Zhang
*/
public class gotoAnalyzer {
	
	/**
	 * The name pattern for the directory containing the graphs for the processed goto.
	 * <p>
	 * 1- The {@link SourceCorrespondence}.
	 */
	private static final String GOTO_GRAPH_DIRECTORY_NAME_PATTERN = "gotoAnalyze_graphs";
	
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
	private static final String CFG_GRAPH_FILE_NAME_PATTERN = "CFG@%s@%s@%s";
	private static final String PCG_GRAPH_FILE_NAME_PATTERN = "PCG@%s@%s@%s";
	
	public gotoAnalyzer()
	{
		this.graphsOutputDirectory = VerificationProperties.getGraphsOutputDirectory();
		
	}
	
	private static void saveDisplayCFG(Graph cfgGraph, String sourceFile, String methodName, Markup markup, boolean displayGraphs) { 
        if(displayGraphs){
            DisplayUtil.displayGraph(markup, cfgGraph);
        }
            
        try{
            String cfgFileName = String.format(CFG_GRAPH_FILE_NAME_PATTERN, sourceFile, methodName, VerificationProperties.getGraphImageFileNameExtension());
            SaveUtil.saveGraph(new File(currentgotoGraphsOutputDirectory, cfgFileName), cfgGraph, markup).join();
        } catch (InterruptedException e) {}
            
    }	
	
	private static void saveDisplayPCG(Graph pcgGraph, String sourceFile, String methodName, Markup markup, boolean displayGraphs) { 
        if(displayGraphs){
            DisplayUtil.displayGraph(markup, pcgGraph);
        }
            
        try{
            String pcgFileName = String.format(PCG_GRAPH_FILE_NAME_PATTERN, sourceFile, methodName, VerificationProperties.getGraphImageFileNameExtension());
            SaveUtil.saveGraph(new File(currentgotoGraphsOutputDirectory, pcgFileName), pcgGraph, markup).join();
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
	
	public static void analyzeGotos() {
		
		new gotoAnalyzer().createDirectory();
		
		Q functions = Common.universe().nodesTaggedWithAny(XCSG.Function);
		
//		AtlasSet<Node> funSet = new AtlasHashSet<Node>();
		for(Node function: functions.eval().nodes()) {
//			Log.info("Processing " + function.getAttr(XCSG.name));

			Q func_q = Common.toQ(function);
			// parse the function
			
			process_func(func_q);
			
		}
	}
	
	private static void process_func(Q function) {
		Node func_node = function.eval().nodes().getFirst();
		
		Q cfg = CommonQueries.cfg(function);
		Q label_nodes = CommonQueries.nodesStartingWith(cfg, "label ");
		
		AtlasSet<Node> label_set = new AtlasHashSet<Node>();
		AtlasSet<Node> goto_set = new AtlasHashSet<Node>();
		
		for(Node label:label_nodes.eval().nodes()) {
			AtlasSet<Node> goto_pred_set = CommonQueries.nodesStartingWith(cfg.predecessors(Common.toQ(label)), "goto ").eval().nodes();
			
			if(goto_pred_set.size() > 1) {
				label_set.add(label);
				goto_set.addAll(goto_pred_set);
			}
		}
		
//		Log.info(func_node.getAttr(XCSG.name).toString()+"||"+label_set.size());
		if(label_set.size() <1) {
			
			return;
		}
		
		Log.info(func_node.getAttr(XCSG.name).toString());
		
		// mark up
		Markup markup = new Markup();
		markup.set(Common.toQ(goto_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW);
		markup.set(Common.toQ(label_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.RED);
		
		// set file name
		String sourceFile = getQualifiedFunctionName(func_node);
		String methodName =  func_node.getAttr(XCSG.name).toString();
		
		Log.info("SOURCE: "+sourceFile);
		Log.info("NAME: "+methodName);
		
		// output CFG
		saveDisplayCFG(cfg.eval(),sourceFile, methodName, markup, false);
		
		// get PCG seeds
		Q control_nodes = cfg.nodes(XCSG.ControlFlowCondition);
		AtlasSet<Node> pcg_seeds = control_nodes.union(Common.toQ(goto_set)).union(Common.toQ(label_set)).eval().nodes();
		
		// output PCG
		Markup markup2 = new Markup();
		
		markup2.set(Common.toQ(goto_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.YELLOW);
		markup2.set(Common.toQ(label_set), MarkupProperty.NODE_BACKGROUND_COLOR, Color.RED);
		Q pcg = PCGFactory.create(cfg, Common.toQ(pcg_seeds)).getPCG();
		saveDisplayPCG(pcg.eval(), sourceFile, methodName, markup2, false);
		
	}

	
}
