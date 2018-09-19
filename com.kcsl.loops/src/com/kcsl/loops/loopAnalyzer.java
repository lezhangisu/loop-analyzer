package com.kcsl.loops;


import com.ensoftcorp.atlas.core.db.graph.Graph;
import com.ensoftcorp.atlas.core.db.graph.Node;
import com.ensoftcorp.atlas.core.db.set.AtlasSet;
import com.ensoftcorp.atlas.core.markup.Markup;
import com.ensoftcorp.atlas.core.query.Q;
import com.ensoftcorp.atlas.core.script.Common;
import com.ensoftcorp.atlas.core.xcsg.XCSG;
import com.ensoftcorp.atlas.ui.viewer.graph.DisplayUtil;
import com.ensoftcorp.atlas.ui.viewer.graph.SaveUtil;
import com.ensoftcorp.atlas.core.script.CommonQueries;

import com.kcsl.loops.log.Log;

/**
* This program checks if a given function or all functions in mapped workspace are structured
* It parses through all the control flow condition nodes and obtain the subgraph under them
* If the subgraph has more than one entries, it is unstructured.
*
* @author Le Zhang
*/
public class loopAnalyzer {
	
//	private static void saveDisplayCFG(Graph cfgGraph, String sourceFile, String methodName, Markup markup, boolean displayGraphs) { 
//        if(displayGraphs){
//            DisplayUtil.displayGraph(markup, cfgGraph);
//        }
//            
//        try{
//            String cfgFileName = String.format(CFG_GRAPH_FILE_NAME_PATTERN, sourceFile,methodName, VerificationProperties.getGraphImageFileNameExtension());
//            SaveUtil.saveGraph(new File(currentgotoGraphsOutputDirectory, cfgFileName), cfgGraph, markup).join();
//        } catch (InterruptedException e) {}
//            
//    }	
//	
//	private  void createContainingDirectory(){
//        String containingDirectoryName = String.format(GOTO_GRAPH_DIRECTORY_NAME_PATTERN);
//        currentgotoGraphsOutputDirectory = this.graphsOutputDirectory.resolve(containingDirectoryName).toFile();
//        if(!currentgotoGraphsOutputDirectory.exists())
//        {
//        if(!currentgotoGraphsOutputDirectory.mkdirs()){
//            Log.info("Cannot create directory:" + currentgotoGraphsOutputDirectory.getAbsolutePath());
//        }
//        }
//    }
	public static void tagLoops() {
		Q q = Common.universe().nodesTaggedWithAny(XCSG.Loop);
		long loopCnt = q.eval().nodes().size();
//		Log.info("Loop Count Before: "+loopCnt);
		com.ensoftcorp.open.jimple.commons.loops.DecompiledLoopIdentification.recoverLoops();
		loopCnt = q.eval().nodes().size();
//		Log.info("Loop Count: "+loopCnt);
		Q q2 = CommonQueries.nodesStartingWith(q, "label ");
		loopCnt = q2.eval().nodes().size();
//		Log.info("Loops Formed by GOTO: " + loopCnt);
		
		
		Q functions = q.containers().nodes(XCSG.Function);
		AtlasSet<Node> function_set = functions.eval().nodes();
		
//		for(Node function : function_set) {
//			Log.info(function.getAttr(XCSG.name).toString());
//		}
		
		
		AtlasSet<Node> function_goto_loop_set = q2.containers().nodes(XCSG.Function).eval().nodes();
		for(Node function : function_goto_loop_set) {
			Log.info(function.getAttr(XCSG.name).toString());
		}
		
		Log.info("=======================");
		Log.info("Total loops: " + q.eval().nodes().size());
		Log.info("Total Functions have loops: " + function_set.size());
		Log.info("=======================");
		
		Log.info("Total Loops Formed by GOTO: " + loopCnt);
		Log.info("Total Functions have GOTO loops: " + function_goto_loop_set.size());
		Log.info("=======================");
		
	}
	
}
