/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.cpachecker.cpa.bam.incremental.program;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;

/**
 * @author jeremy
 *
 */
public class FunctionInfo implements Serializable {
  private static final long serialVersionUID = 132323232L;
  private String name;
  private HashSet<String> calledFunctionName;
  private String functionBody;
  private Collection<Integer> returnNodes;
  private int lineNum;
  private boolean isChanged = false;

  public FunctionInfo(String pName, String pFunctionBody) {
    super();
    name = pName;
    calledFunctionName = new HashSet<>();
    functionBody = pFunctionBody;
    lineNum = functionBody.split("\\n").length;
    ProgramInfo.getInstance().addFuncLineMap(pName, lineNum);
  }

  public String getName() {
    return name;
  }

  public void setName(String pName) {
    name = pName;
  }

  public HashSet<String> getCalledFunctionName() {
    return calledFunctionName;
  }

  public void setCalledFunctionName(HashSet<String> pCalledFunctionName) {
    calledFunctionName = new HashSet<>(pCalledFunctionName);
  }

  public void addCalledFunctionName(String fN) {
    calledFunctionName.add(fN);
  }

  public String getFunctionBody() {
    return functionBody;
  }

  public void setFunctionBody(String pFunctionBody) {
    functionBody = pFunctionBody;
  }

  public Collection<Integer> getReturnNodes() {
    return returnNodes;
  }

  public void setReturnNodes(Collection<Integer> pReturnNodes) {
    returnNodes = pReturnNodes;
  }


  public boolean isChanged() {
    return isChanged;
  }

  public void setChanged(boolean pIsChanged) {
    isChanged = pIsChanged;
  }

  public int getLineNum() {
    return lineNum;
  }

  public void setLineNum(int pLineNum) {
    lineNum = pLineNum;
  }

  @Override
  public String toString() {
    return "\n" + getName() + "\n" +
        getFunctionBody() + "\n";
  }
}
