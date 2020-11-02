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
package org.sosy_lab.cpachecker.cpa.bam.incremental;

import java.util.ArrayList;
import java.util.List;

import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;


public class InputOutputType {
  private List<Pair<Byte, Byte>> inputList;
  private List<Pair<Byte, Byte>> outputList;

  public InputOutputType(ValueAnalysisState state) {
    inputList = new ArrayList<>();
    outputList = new ArrayList<>();
  }

  public void addInputPair(byte valueType, byte numberType) {
    inputList.add(Pair.of(valueType, numberType));
  }

  public void addOutputPair(byte valueType, byte numberType) {
    outputList.add(Pair.of(valueType, numberType));
  }

  @Override
  public String toString() {
    StringBuilder builder = new StringBuilder();
    if(inputList.size() > 0) {
      builder.append(inputList.get(0).getFirst() + "," + inputList.get(0).getSecond());
      for(int i = 1; i < inputList.size(); i++) {
        Pair<Byte, Byte> curPair = inputList.get(i);
        builder.append("IT" + curPair.getFirst() + "," + curPair.getSecond());
      }
    }
    builder.append("IOT");
    if(outputList.size() > 0) {
      builder.append(outputList.get(0).getFirst() + "," + outputList.get(0).getSecond());
      for(int i = 1; i < outputList.size(); i++) {
        Pair<Byte, Byte> curPair = outputList.get(i);
        builder.append("OT" + curPair.getFirst() + "," + curPair.getSecond());
      }
    }
    return builder.toString();
  }

}
