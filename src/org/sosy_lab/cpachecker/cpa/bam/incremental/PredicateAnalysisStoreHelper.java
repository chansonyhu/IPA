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

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.sosy_lab.cpachecker.cfa.types.c.CNumericTypes;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap.SSAMapBuilder;
import org.sosy_lab.cpachecker.util.predicates.pathformula.pointeraliasing.PointerTargetSet;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.IOUtil;

public class PredicateAnalysisStoreHelper implements StoreHelper {

  @Override
  public String stateToString(AbstractState pState, String funName) {
    PredicateAbstractState predicateAbstractState = (PredicateAbstractState)getRealState(pState);
    FormulaManagerView managerView = GlobalInfo.getInstance().getFormulaManagerView();
    return managerView.dumpFormula(predicateAbstractState.getAbstractionFormula().asFormula()).toString();
  }

  @Override
  public void serializeState(AbstractState pState, FormulaManager manager) throws IOException {
    PredicateAbstractState predicateAbstractState = (PredicateAbstractState)getRealState(pState);
    BooleanFormula formula = predicateAbstractState.getAbstractionFormula().asFormula();
    manager.serializeFormula(formula);
  }

  @Override
  public AbstractState resolveState(String pCurFName, FormulaManager manager) throws IOException {
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
    AbstractionManager abstractionManager = GlobalInfo.getInstance().getAbstractionManager();
    BooleanFormula booleanFormula = manager.resolveFormula();
    PathFormula pathFormula = new PathFormula(formulaManagerView.getBooleanFormulaManager().makeBoolean(true), SSAMap.emptySSAMap(), PointerTargetSet.emptyPointerTargetSet(), 0);
    AbstractionFormula abstractionFormula = new AbstractionFormula(formulaManagerView, abstractionManager.getRegionCreator().makeTrue(), booleanFormula, booleanFormula, pathFormula, new HashSet<Integer>());
    return PredicateAbstractState.mkAbstractionState(null, abstractionFormula, null);
  }

  @Override
  public AbstractState resolveState(String pCurFName, FormulaManager manager, SSAMap ssaMap) throws IOException {
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
    AbstractionManager abstractionManager = GlobalInfo.getInstance().getAbstractionManager();
    BooleanFormula booleanFormula = manager.resolveFormula();
    PathFormula pathFormula = new PathFormula(formulaManagerView.getBooleanFormulaManager().makeBoolean(true), ssaMap, PointerTargetSet.emptyPointerTargetSet(), 0);
    AbstractionFormula abstractionFormula = new AbstractionFormula(formulaManagerView, abstractionManager.getRegionCreator().makeTrue(), booleanFormula, booleanFormula, pathFormula, new HashSet<Integer>());
    return PredicateAbstractState.mkAbstractionState(null, abstractionFormula, null);
  }

  @Override
  public AbstractState buildStateFromString(String pCurFName, String pStr) {
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
    AbstractionManager abstractionManager = GlobalInfo.getInstance().getAbstractionManager();
    BooleanFormula booleanFormula = formulaManagerView.parse(pStr);
//    formulaManagerView.instantiate(booleanFormula, );   don't ssamap
    //only pFormula is useful
    PathFormula pathFormula = new PathFormula(formulaManagerView.getBooleanFormulaManager().makeBoolean(true), SSAMap.emptySSAMap(), PointerTargetSet.emptyPointerTargetSet(), 0);
    AbstractionFormula abstractionFormula = new AbstractionFormula(formulaManagerView, abstractionManager.getRegionCreator().makeTrue(), booleanFormula, booleanFormula, pathFormula, new HashSet<Integer>());
    return PredicateAbstractState.mkAbstractionState(null, abstractionFormula, null);
  }

  @Override
  public AbstractState buildStateFromString(String pCurFName, String pStr, SSAMap ssaMap) {
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
    AbstractionManager abstractionManager = GlobalInfo.getInstance().getAbstractionManager();
    BooleanFormula booleanFormula = formulaManagerView.parse(pStr);
    PathFormula pathFormula = new PathFormula(formulaManagerView.getBooleanFormulaManager().makeBoolean(true), ssaMap, PointerTargetSet.emptyPointerTargetSet(), 0);
    AbstractionFormula abstractionFormula = new AbstractionFormula(formulaManagerView, abstractionManager.getRegionCreator().makeTrue(), booleanFormula, booleanFormula, pathFormula, new HashSet<Integer>());
    return PredicateAbstractState.mkAbstractionState(null, abstractionFormula, null);
  }

  @Override
  public AbstractState getRealState(AbstractState pState) {
    AbstractState result = AbstractStates.extractStateByType(pState, PredicateAbstractState.class);
    return result;
  }

  @Override
  public LocationState getLocationState(AbstractState pState) {
    return AbstractStates.extractStateByType(pState, LocationState.class);
  }

  @Override
  public String getOthers(AbstractState pInputState, Collection<AbstractState> pOutputStates) {
    StringBuilder ansBuilder = new StringBuilder();
    Map<String, Integer> variableMap = getVariableType(pInputState, pOutputStates);
    for(Entry<String, Integer> curE : variableMap.entrySet()) {
      ansBuilder.append(curE.getKey() + ";" + curE.getValue() + ",,");
    }
    if(variableMap.entrySet().size() > 0) {
      return ansBuilder.substring(0, ansBuilder.length() - 2);
    }
    return ansBuilder.toString();
  }

  @Override
  public void serializeOthers(AbstractState pInputState, Collection<AbstractState> pOutputStates, DataOutputStream out, FormulaManager manager) throws IOException {
    Map<String, Integer> variableMap = getVariableType(pInputState, pOutputStates);
    IOUtil.writeVInt(out, variableMap.size());
    for(Entry<String, Integer> curE : variableMap.entrySet()) {
      int keyInt = manager.addSerializeDictionary(FormulaManager.FVARTYPE, curE.getKey());
      IOUtil.writeVInt(out, keyInt);
      IOUtil.writeVInt(out, curE.getValue());
    }
  }

  @Override
  public SSAMap resolveOthers(DataInputStream in, FormulaManager manager) throws IOException {
    SSAMapBuilder builder = SSAMap.emptySSAMap().builder();
    int size = IOUtil.readVInt(in);
    for(int i = 0; i < size; i++) {
      int keyInt = IOUtil.readVInt(in);
      int typeInt = IOUtil.readVInt(in);
      builder.setIndex(manager.getResolveDictionary(FormulaManager.FVARTYPE, keyInt), intToCType(typeInt), 1);
    }
    return builder.build();
  }

  @Override
  public SSAMap convertOthersToSSAMAP(String others) {
    SSAMapBuilder builder = SSAMap.emptySSAMap().builder();
    if(others == null || others.trim().length() == 0) {
      return builder.build();
    }
    String[] otherSplits = others.replace("\n", "").split(",,");
    for(String curS : otherSplits) {
      String[] curSplit = curS.split(";");
      String name = curSplit[0];
      int typeI = Integer.parseInt(curSplit[1]);
      CType type = intToCType(typeI);
      builder.setIndex(name, type, 1);
    }
    return builder.build();
  }

  private Map<String, Integer> getVariableType(AbstractState pInputState, Collection<AbstractState> pOutputStates) {
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
//    PredicateAbstractState inputPState = (PredicateAbstractState)getRealState(pInputState);
//    SSAMap inputSSAMap = inputPState.getAbstractionFormula().getBlockFormula().getSsa();
    Map<String, Integer> ansMap = new HashMap<>();
    for(AbstractState curState : pOutputStates) {
      PredicateAbstractState curPState = (PredicateAbstractState)getRealState(curState);
      SSAMap curSSAMap = curPState.getAbstractionFormula().getBlockFormula().getSsa();

//      for(String curS : curSSAMap.allVariables()) {
//        if(!inputSSAMap.containsVariable(curS)) {
//          ansMap.put(curS, ctypeToInt(curSSAMap.getType(curS)));
//        }
//      }

      BooleanFormula curFormula = curPState.getAbstractionFormula().asFormula();
      Set<String> allVariables = formulaManagerView.extractVariableNames(curFormula);

      for(String curS : allVariables) {
        if(curSSAMap.getType(curS) == null) {
          System.out.println("ctype to int error: null exception, variable name:" + curS);
        }
        ansMap.put(curS, ctypeToInt(curSSAMap.getType(curS)));
      }
    }
    return ansMap;
  }

  private int ctypeToInt(CType type) {
    if(type == null) {
      return 10;
    }
    if(type.equals(CNumericTypes.BOOL)) {
      return 0;
    }
    if(type.equals(CNumericTypes.CHAR)) {
      return 1;
    }
    if(type.equals(CNumericTypes.DOUBLE)) {
      return 2;
    }
    if(type.equals(CNumericTypes.FLOAT)) {
      return 3;
    }
    if(type.equals(CNumericTypes.INT)) {
      return 4;
    }
    if(type.equals(CNumericTypes.LONG_DOUBLE)) {
      return 5;
    }
    if(type.equals(CNumericTypes.LONG_INT)) {
      return 6;
    }
    if(type.equals(CNumericTypes.LONG_LONG_INT)) {
      return 7;
    }
    if(type.equals(CNumericTypes.SHORT_INT)) {
      return 8;
    }
    if(type.equals(CNumericTypes.SIGNED_CHAR)) {
      return 9;
    }
    if(type.equals(CNumericTypes.SIGNED_INT)) {
      return 10;
    }
    if(type.equals(CNumericTypes.UNSIGNED_CHAR)) {
      return 11;
    }
    if(type.equals(CNumericTypes.UNSIGNED_INT)) {
      return 12;
    }
    if(type.equals(CNumericTypes.UNSIGNED_LONG_INT)) {
      return 13;
    }
    if(type.equals(CNumericTypes.UNSIGNED_LONG_LONG_INT)) {
      return 14;
    }
    if(type.equals(CNumericTypes.UNSIGNED_SHORT_INT)) {
      return 15;
    }
    return 16;
  }

  private CType intToCType(int type) {
    switch (type) {
    case 0:
      return CNumericTypes.BOOL;
    case 1:
      return CNumericTypes.CHAR;
    case 2:
      return CNumericTypes.DOUBLE;
    case 3:
      return CNumericTypes.FLOAT;
    case 4:
      return CNumericTypes.INT;
    case 5:
      return CNumericTypes.LONG_DOUBLE;
    case 6:
      return CNumericTypes.LONG_INT;
    case 7:
      return CNumericTypes.LONG_LONG_INT;
    case 8:
      return CNumericTypes.SHORT_INT;
    case 9:
      return CNumericTypes.SIGNED_CHAR;
    case 10:
      return CNumericTypes.SIGNED_INT;
    case 11:
      return CNumericTypes.UNSIGNED_CHAR;
    case 12:
      return CNumericTypes.UNSIGNED_INT;
    case 13:
      return CNumericTypes.UNSIGNED_LONG_INT;
    case 14:
      return CNumericTypes.UNSIGNED_LONG_LONG_INT;
    case 15:
      return CNumericTypes.UNSIGNED_SHORT_INT;
    default:
      return CNumericTypes.DOUBLE;
    }
  }

}
