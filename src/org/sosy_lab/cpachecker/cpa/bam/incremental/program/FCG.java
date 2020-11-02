package org.sosy_lab.cpachecker.cpa.bam.incremental.program;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class FCG {
	public static Set<String> history = new HashSet<>();

	public static void createFunctionCallGraphAndUpdateChanges(FunctionNode curNode, HashMap<String, FunctionInfo> nameInfoMap) {
		if(curNode == null || curNode.getFunctionInfo() == null) {
      return;
    }
		FunctionInfo curInfo = curNode.getFunctionInfo();
		updateFunctionChanged(curNode);

		for(String calledName : curInfo.getCalledFunctionName()) {
			FunctionInfo callInfo = nameInfoMap.get(calledName);
			FunctionNode callNode = new FunctionNode(callInfo);
			callNode.setParentNode(curNode);
			curNode.addChildNodes(callNode);
			if(history.contains(calledName)) {
				history.clear();
				break;
			} else {
				history.add(calledName);
			}
			createFunctionCallGraphAndUpdateChanges(callNode, nameInfoMap);
		}
	}

	private static void updateFunctionChanged(FunctionNode fNode)
	{
		if(fNode.getFunctionInfo() != null)
		{
			if(fNode.getFunctionInfo().isChanged())
			{
				FunctionNode curNode = fNode.getParentNode();
				while(curNode != null)
				{
					curNode.getFunctionInfo().setChanged(true);
					curNode = curNode.getParentNode();
				}
			}
		}
	}

}
