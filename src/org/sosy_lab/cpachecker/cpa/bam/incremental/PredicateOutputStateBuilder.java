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
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.SortedSet;

import java.util.concurrent.TimeUnit;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.common.time.TimeSpan;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.types.c.CNumericTypes;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.core.MainCPAStatistics;
import org.sosy_lab.cpachecker.core.algorithm.CEGARAlgorithm;
import org.sosy_lab.cpachecker.core.algorithm.CEGARAlgorithm.CEGARStatistics;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.automaton.AutomatonState;
import org.sosy_lab.cpachecker.cpa.callstack.CallstackState;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.functionpointer.FunctionPointerState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.BooleanFormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap.SSAMapBuilder;

public class PredicateOutputStateBuilder implements OutputStateBuilder {

  @Override
  public Collection<AbstractState> buildOutputState(final ARGState inputState,
                                             Pair<Collection<AbstractState>, Collection<Integer>> pOutput) {
    checkArgument(false);
    return Collections.singleton(null);
  }

  @Override
  public Collection<AbstractState> buildOutputState(ARGState pInputState, Pair<Collection<AbstractState>, Collection<Integer>> pOutput, Set<CFANode> returnNodes) {

    Iterator<CFANode> returnNode = returnNodes.iterator();

    List<AbstractState> targetStates = new ArrayList<>();
    Collection<AbstractState> pOutputStates = pOutput.getFirst();
    Collection<Integer> pOutputLocations = pOutput.getSecond();
    Iterator<AbstractState> state = pOutputStates.iterator();
    Iterator<Integer> location = pOutputLocations.iterator();
    Boolean more = false;
    Boolean isMultiState = false;
    if(pOutputStates.size() > 1) {
      if(returnNodes.size() == 1) {
        for (Object l:
          pOutputLocations.toArray()) {
          if((Integer)l != (Integer)pOutputLocations.toArray()[0]) {
            more = true;
            break;
          }
        }
        isMultiState = true;
        more = false;
      } else {
        more = true;
        System.out.println("output states larger than 1......");
      }
    }

    AbstractionManager abstractionManager = GlobalInfo.getInstance().getAbstractionManager();
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
    while(state.hasNext() && location.hasNext()) {
      List<AbstractState> elements = new ArrayList<>();
      LocationState locationState = AbstractStates.extractStateByType(pInputState, LocationState.class);
      CFANode node = locationState.getLocationNode();
      int id;
      /**if(!(node.getFunctionName().contains(CPAMain.entryFunction) || node.getFunctionName().contains("loop")))
       id = node.getNodeNumber() - 1;
       else if(CFANode.isBelongtoLoopBlock(node))
       id = location.next();
       else id = location.next();**/
      id = location.next();
      int tmp;
      try {
         tmp = (returnNode.next()).getNodeNumber();
      } catch (NoSuchElementException e) {
        if(isMultiState) {
          tmp = ((CFANode) returnNodes.toArray()[0]).getNodeNumber();
        } else {
          break;
        }
      }
      if(id != tmp) {
        // System.out.println("Unmatching CFA node");
        GlobalInfo.getInstance().umc += 1;
        int threshold = 0;
        threshold = RefineHelper.pathLens * GlobalInfo.getInstance().umc * CEGARStatistics.countRefinements / 100;
        if(GlobalInfo.getInstance().umc > GlobalInfo.MAX_UMC && threshold > GlobalInfo.restart_threshold) {

//          String total = TimeSpan.ofNanos(MainCPAStatistics.analysisCpuTime).formatAs(TimeUnit.SECONDS);
//          total = total.split("s")[0];
//          float cputime = Float.parseFloat(total);

            IncrementalCache.getInstance().clearSummaryCache();
        }
        checkArgument(returnNodes.size() == 1);
//        if(returnNodes.size() > 1)
//          System.out.println("Unresolved issue: Unmatching CFA node large than 1.");
        id = tmp;
      }
      LocationState exitLocationState = LocationState.getLocationStateByID(id, node);
      elements.add(exitLocationState);

      CallstackState callstackState = AbstractStates.extractStateByType(pInputState, CallstackState.class);
      elements.add(callstackState);
      FunctionPointerState functionPointerState = AbstractStates.extractStateByType(pInputState, FunctionPointerState.class);
      elements.add(functionPointerState);

      PredicateAbstractState predicateAbstractState = AbstractStates.extractStateByType(pInputState, PredicateAbstractState.class);

      PredicateAbstractState cachePredicateAbstractState = (PredicateAbstractState) state.next();
      BooleanFormula formula = cachePredicateAbstractState.getAbstractionFormula().asFormula();
      Region region = null;
      try{
        //if(formula.toString().contains("distinct")){
        //  if(abstractionManager.getPredicate(formula) == null)
        //    abstractionManager.makePredicate(formula);
        //}
        //if(!formula.toString().contains("false") && !formula.toString().equals("true"))
        //  if(abstractionManager.getPredicate(formula) == null)
        //    abstractionManager.makePredicate(formula);
        region = abstractionManager.buildRegionFromFormula(formula);
      } catch (IllegalArgumentException e){
        /*if(iterator.hasNext()) {
          cachePredicateAbstractState = (PredicateAbstractState) iterator.next();
          formula = cachePredicateAbstractState.getAbstractionFormula().asFormula();
          try {
            region = abstractionManager.buildRegionFromFormula(formula);
          } catch (IllegalArgumentException e1) {
            return null;
          }
        }*/
        //e.printStackTrace();
        System.out.println("Cannot build region for " + formula.toString());
        return null;
      }
      if(region == null) {
        return null;
      }
      SSAMap inputSSAMAP = predicateAbstractState.getAbstractionFormula().getBlockFormula().getSsa();
      Set<String> variableNames = formulaManagerView.extractVariableNames(formula);
      SSAMap outputSSAMAP = buildOutputStateSSAMap(inputSSAMAP, cachePredicateAbstractState.getAbstractionFormula().getBlockFormula().getSsa(), variableNames);
      BooleanFormula instantiatedFormula = formulaManagerView.instantiate(formula, outputSSAMAP);

      PathFormula pathFormula0 = cachePredicateAbstractState.getAbstractionFormula().getBlockFormula();

      PathFormula pathFormula = new PathFormula(pathFormula0.getFormula(), outputSSAMAP, pathFormula0.getPointerTargetSet(), pathFormula0.getLength());

      Set<Integer> reuseIds = predicateAbstractState.getAbstractionFormula().getIdsOfStoredAbstractionReused();
      AbstractionFormula abstractionFormula = new AbstractionFormula(formulaManagerView, region, formula, instantiatedFormula, pathFormula, reuseIds);

      PersistentMap<CFANode, Integer> abstractionLocationPaths = predicateAbstractState.getAbstractionLocationsOnPath().putAndCopy(exitLocationState.getLocationNode(), 1);
      PathFormula outOldPathFormula = predicateAbstractState.getPathFormula();
      PathFormula outPathFormula = new PathFormula(outOldPathFormula.getFormula(), outputSSAMAP, outOldPathFormula.getPointerTargetSet(), outOldPathFormula.getLength());
      PredicateAbstractState newPredicateAbstractState = PredicateAbstractState.mkAbstractionState(outPathFormula, abstractionFormula, abstractionLocationPaths);
      elements.add(newPredicateAbstractState);

      AutomatonState automatonState = AbstractStates.extractStateByType(pInputState, AutomatonState.class);
      elements.add(automatonState);

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
    assert  pOutputStates.size() == targetStates.size() : "incomplete output state";
    return targetStates;
  }

  private SSAMap buildOutputStateSSAMap(SSAMap inputSSAMap, SSAMap cachedSSAMAP, Set<String> variableNames) {
    SSAMapBuilder builder = SSAMap.emptySSAMap().builder();
    SortedSet<String> variables = inputSSAMap.allVariables();
    for(String curV : variables) {
      builder.setIndex(curV, inputSSAMap.getType(curV), inputSSAMap.getIndex(curV) + 1);
    }
    for(String curV : variableNames) {
      if(!variables.contains(curV)) {
        CType variableType = cachedSSAMAP.getType(curV);
        if(variableType == null) {
          variableType = CNumericTypes.INT;
        }
        builder.setIndex(curV, variableType, 2);
      }
    }
    return builder.build();
  }

}
