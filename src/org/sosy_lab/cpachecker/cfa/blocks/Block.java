/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cfa.blocks;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import java.util.Vector;
import java.util.logging.Level;
import org.sosy_lab.cpachecker.cfa.model.CFANode;

import com.google.common.collect.ImmutableSet;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionEntryNode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.FunctionInfo;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.ProgramInfo;

/**
 * Represents a block as described in the BAM paper.
 */
public class Block {

  private final ImmutableSet<ReferencedVariable> referencedVariables;
  private final ImmutableSet<CFANode> callNodes;
  private final ImmutableSet<CFANode> returnNodes;
  private final ImmutableSet<CFANode> nodes;
  private final String functionName;
  private String uniqueName;

  public Block(Set<ReferencedVariable> pReferencedVariables,
      Set<CFANode> pCallNodes, Set<CFANode> pReturnNodes, Set<CFANode> allNodes) {

    referencedVariables = ImmutableSet.copyOf(pReferencedVariables);
    callNodes = ImmutableSet.copyOf(pCallNodes);
    returnNodes = ImmutableSet.copyOf(pReturnNodes);
    nodes = ImmutableSet.copyOf(allNodes);
    functionName = callNodes.iterator().next().getFunctionName();

    setUniqueName();
    saveReturnNodes();
    if(getUniqueName().equals("loop-1"))
      throw new NullPointerException();
  }

  public Block(String funcName) {
    referencedVariables = ImmutableSet.of();
    callNodes = ImmutableSet.of();
    returnNodes = ImmutableSet.of();
    nodes = ImmutableSet.of();
    functionName = funcName;
    setUniqueName();
  }
  private void saveReturnNodes() {
    ArrayList<Integer> returns = new ArrayList<>();
    for(CFANode node : returnNodes) {
      returns.add(node.getNodeNumber());
    }
    Collections.sort(returns);
    assert(ProgramInfo.getInstance().getNowFunctionInfo().get(uniqueName) != null);
    ProgramInfo.getInstance().getNowFunctionInfo().get(uniqueName).setReturnNodes(returns);
  }
  private void setUniqueName() {
    //TODO qianshan
    if(CPAMain.onlyFunctionSummary) {
      uniqueName = functionName;
      return;
    }
    switch (blockType()){
      case 0: uniqueName = "main";break;
      case 1: uniqueName = functionName; break;
      case 2:
        int loopNumber = -1;
        int benchNumber = -1;
        for(CFANode node : callNodes) {
          if(node.isLoopStart()) {
            loopNumber = node.getNodeNumber() - 1;
            break;
          } else {
            benchNumber = node.getNodeNumber();
            break;
          }
        }
        if(loopNumber == -1) {
          Vector<Integer> loops = new Vector<>();
          HashMap<String, FunctionInfo> nowFunc = ProgramInfo.getInstance().getNowFunctionInfo();
          for(Map.Entry<String, FunctionInfo> entry : nowFunc.entrySet()) {
            if(entry.getKey().startsWith("loop")){
              loops.add(Integer.parseInt(entry.getKey().substring(4)));
            }
          }
          int min = Integer.MAX_VALUE;
          for(Integer i : loops){
            if(Math.abs(i - benchNumber) < min) {
              min = Math.abs(i - benchNumber);
              loopNumber = i;
            }
          }
        }
        uniqueName = "loop" + loopNumber;
        CPAMain.logManager.log(Level.INFO, "approx loop is " + loopNumber + " , " + benchNumber);
        CPAMain.logManager.log(Level.INFO, loopNumber);
        break;
      default: uniqueName = functionName;
    }

  }
  //TODO qianshan
  //public String getFunctionName() {
  //  return functionName;
  //}

  public String getFunctionName() {
    if(!CPAMain.onlyFunctionSummary)
      return uniqueName;
    else
      return functionName;
  }

  public Set<CFANode> getCallNodes() {
    return Collections.unmodifiableSet(callNodes);
  }

  public CFANode getCallNode() {
    assert callNodes.size() == 1;
    return callNodes.iterator().next();
  }

  public Set<ReferencedVariable> getReferencedVariables() {
    return referencedVariables;
  }

  public Set<CFANode> getNodes() {
    return nodes;
  }

  public boolean isReturnNode(CFANode pNode) {
    return returnNodes.contains(pNode);
  }

  public Set<CFANode> getReturnNodes() {
    return returnNodes;
  }

  public boolean isCallNode(CFANode pNode) {
    return callNodes.contains(pNode);
  }

  @Override
  public String toString() {
    return "Block " +
            "(CallNodes: " + callNodes + ") " +
            "(Nodes: " + (nodes.size() < 10 ? nodes : "[#=" + nodes.size() + "]") + ") " +
            "(ReturnNodes: " + returnNodes + ")";
  }

  //TODO qianshan. Add the following functions
  public Boolean isMainBlock() {
    for(CFANode node : callNodes) {
      if(node instanceof CFunctionEntryNode && ((CFunctionEntryNode) node).getFunctionDefinition().getName().equals("main"))
        return true;
    }
    return false;
  }
  public Boolean isLoopBlock() {
    for(CFANode node : callNodes)
      if(node.isLoopStart()) return true;
    if (!isFunctionBlock() && !isMainBlock()) return true;
    return false;
  }
  public Boolean isFunctionBlock() {
    for(CFANode node : callNodes) {
      if(node instanceof CFunctionEntryNode && !((CFunctionEntryNode) node).getFunctionDefinition().getName().equals("main"))
        return true;
    }
    return false;
  }
  public int blockType() {
    if(this.isMainBlock()) return 0;
    else if(this.isFunctionBlock()) return 1;
    else if(this.isLoopBlock()) return 2;
    return -1;
  }
  private String getUniqueName(){
    return uniqueName;
  }
}
