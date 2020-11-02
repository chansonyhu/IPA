package org.sosy_lab.cpachecker.cpa.bam.incremental.program;

import java.util.ArrayList;

public class FunctionNode {
	private FunctionInfo functionInfo;
	private FunctionNode parentNode;
	private ArrayList<FunctionNode> childNodes;

	public FunctionNode(FunctionInfo functionInfo)
	{
		this.functionInfo = functionInfo;
		childNodes = new ArrayList<FunctionNode>();
	}

	public FunctionInfo getFunctionInfo() {
		return functionInfo;
	}

	public FunctionNode getParentNode() {
		return parentNode;
	}

	public void setParentNode(FunctionNode parentNode) {
		this.parentNode = parentNode;
	}

	public ArrayList<FunctionNode> getChildNodes() {
		return childNodes;
	}

	public void setChildNodes(ArrayList<FunctionNode> childNodes) {
		this.childNodes = childNodes;
	}

	public void addChildNodes(FunctionNode node)
	{
		this.childNodes.add(node);
	}
}
