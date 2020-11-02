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

import static com.google.common.base.Preconditions.checkArgument;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import java.util.Optional;
import java.util.Set;
import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.automaton.AutomatonState;
import org.sosy_lab.cpachecker.cpa.callstack.CallstackState;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.functionpointer.FunctionPointerState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.util.AbstractStates;

public class ValueAnalysisOutputStateBuilder implements OutputStateBuilder {



  @Override
  public Collection<AbstractState> buildOutputState(final ARGState pInputState, Pair<Collection<AbstractState>, Collection<Integer>> pOutput) {
    List<AbstractState> targetStates = new ArrayList<>();
    Collection<AbstractState> pOutputStates = pOutput.getFirst();
    Collection<Integer> pOutputLocations = pOutput.getSecond();
    Iterator<AbstractState> state = pOutputStates.iterator();
    Iterator<Integer> location = pOutputLocations.iterator();
    //TODO qianshan. 4/21 Comment the following 3 lines
    //if(pOutputStates.size() == 2) {
    //  iterator.next();
    //}
    while(state.hasNext() && location.hasNext()) {
      List<AbstractState> elements = new ArrayList<>();
      LocationState locationState = AbstractStates.extractStateByType(pInputState, LocationState.class);
      CFANode node = locationState.getLocationNode();
      int id;
      /**if(!(node.getFunctionName().contains(CPAMain.entryFunction) || node.getFunctionName().contains("loop")))
       id = node.getNodeNumber() - 1;
       else id = location.next();**/
      id = location.next();
      LocationState exitLocationState = LocationState.getLocationStateByID(id, node);
      elements.add(exitLocationState);

      CallstackState callstackState = AbstractStates.extractStateByType(pInputState, CallstackState.class);
      elements.add(callstackState);
      FunctionPointerState functionPointerState = AbstractStates.extractStateByType(pInputState, FunctionPointerState.class);
      elements.add(functionPointerState);

      ValueAnalysisState valueAnalysisState = AbstractStates.extractStateByType(pInputState, ValueAnalysisState.class);
      ValueAnalysisState cacheValueAnalysisState = (ValueAnalysisState)state.next();
      //TODO qianshan
      ValueAnalysisState newValueAnalysisState = new ValueAnalysisState(cacheValueAnalysisState.getConstantsMap1(), valueAnalysisState.getMemLocToType());
      elements.add(newValueAnalysisState);

      //AutomatonState automatonState = AbstractStates.extractStateByType(pInputState, AutomatonState.class);
      //elements.add(automatonState);

      //TODO bug fixed qianshan
      CompositeState pinput = (CompositeState)(pInputState.getWrappedStates().get(0));
      List<AbstractState> input = pinput.getWrappedStates();
      for(int i=5;i<input.size();i++) {
        elements.add(input.get(i));
      }

      CompositeState pWrappedState = new CompositeState(elements);
      ARGState targetState = new ARGState(pWrappedState, pInputState);
      targetState.addParent(pInputState);
      targetStates.add(targetState);
    }
    assert pOutputStates.size() == targetStates.size() : "incomplete output state";
    return targetStates;
  }

  @Override
  public Collection<AbstractState> buildOutputState(
      ARGState inputState,
      Pair<Collection<AbstractState>, Collection<Integer>> pOutput,
      Set<CFANode> returnNodes) {
    checkArgument(false);
    return null;
  }
}
