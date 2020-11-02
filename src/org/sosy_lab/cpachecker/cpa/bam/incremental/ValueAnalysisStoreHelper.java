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
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collection;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.ProgramInfo;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.cpa.value.type.BooleanValue;
import org.sosy_lab.cpachecker.cpa.value.type.NullValue;
import org.sosy_lab.cpachecker.cpa.value.type.NumericValue;
import org.sosy_lab.cpachecker.cpa.value.type.Value;
import org.sosy_lab.cpachecker.cpa.value.type.Value.UnknownValue;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;

import com.google.common.util.concurrent.AtomicDouble;

public class ValueAnalysisStoreHelper implements StoreHelper {

  @Override
  public String stateToString(AbstractState pState, String funName) {
    Set<String> relativeFunNames = ProgramInfo.getInstance().getRelativeFunMap(funName);
    return ((ValueAnalysisState)pState).toWriteFileString(relativeFunNames);
  }

  @Override
  public AbstractState buildStateFromString(String pCurFName, String pStr) {
    ValueAnalysisState valueAnalysisState = new ValueAnalysisState();
    String[] splits = pStr.split(";");
    for(String curSplit : splits) {
      curSplit = curSplit.replace("<", "").replace(">", "").replace("[", "").replace("]", "");
      if(!curSplit.trim().equals("")) {
        //<a#1=0(3)>
        String[] varSplits = curSplit.split("=");
        assert varSplits.length == 2;

        String[] varNameSplit = varSplits[0].split("#");
        String varName = varNameSplit[0];
//        if(varNameSplit[1].equals("1")) {
//          varName = pCurFName + "::" + varName;
//        }

        StringBuilder varValueBuilder = new StringBuilder();
        int varType = 0;
        int numberType = 10;
        for(int i = 0; i < varSplits[1].length(); i++) {
          char curC = varSplits[1].charAt(i);
          if(curC == '(') {
            varType = varSplits[1].charAt(i + 1) - '0';
            if(varSplits[1].length() > i + 2 && varSplits[1].charAt(i + 2) == ',') {
              numberType = varSplits[1].charAt(i + 3) - '0';
              if(varSplits[1].length() > i + 4 && varSplits[1].charAt(i + 4) != ')') {
                numberType = 10;
              }
            }
            break;
          }
          varValueBuilder.append(curC);
        }
        String varValueString = varValueBuilder.toString();
        Value value = null;
        switch (varType) {
        case 0:
          boolean bValue = false;
          if(varValueString.equals("true")) {
            bValue = true;
          }
          value = BooleanValue.valueOf(bValue);
          break;
        case 1:
          System.err.println("not support enumconstantvalue yet");
          break;
        case 2:
          value = NullValue.getInstance();
          break;
        case 3:
          Number number = null;
          switch (numberType) {
          case 0:
            number = new AtomicDouble(Double.parseDouble(varValueString));
            break;
          case 1:
            number = new AtomicInteger(Integer.parseInt(varValueString));
            break;
          case 2:
            number = new AtomicLong(Long.parseLong(varValueString));
            break;
          case 3:
            number = new Byte(varValueString);
            break;
          case 4:
            number = Double.parseDouble(varValueString);
            break;
          case 5:
            number = Float.parseFloat(varValueString);
            break;
          case 6:
            System.err.println("not support fraction type(Number)");
            break;
          case 7:
            number = Integer.parseInt(varValueString);
            break;
          case 8:
            number = Long.parseLong(varValueString);
            break;
          case 9:
            number = Short.parseShort(varValueString);
            break;
          case 10:
            number = new BigInteger(varValueString);
            break;
          case 11:
            number = new BigDecimal(varValueString);
            break;

          default:
            System.err.println("not support other types(Number)");
          }
          value = new NumericValue(number);
          break;
        case 4:
          value = UnknownValue.getInstance();
          break;
        default:
          break;
        }
        valueAnalysisState.assignConstant(varName, value);
      }
    }
    return valueAnalysisState;
  }

  @Override
  public AbstractState getRealState(AbstractState pState) {
    return AbstractStates.extractStateByType(pState, ValueAnalysisState.class);
  }

  @Override
  public LocationState getLocationState(AbstractState pState) {
    return AbstractStates.extractStateByType(pState, LocationState.class);
  }

  @Override
  public String getOthers(AbstractState pInputState, Collection<AbstractState> pOutputStates) {
    return null;
  }

  @Override
  public AbstractState buildStateFromString(String pCurFName, String pStr, SSAMap pSsaMap) {
    return buildStateFromString(pCurFName, pStr);
  }

  @Override
  public SSAMap convertOthersToSSAMAP(String pOthers) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void serializeState(AbstractState pState, FormulaManager pManager) throws IOException {
    throw new UnsupportedOperationException();
  }

  @Override
  public AbstractState resolveState(String pCurFName, FormulaManager pManager) throws IOException {
    throw new UnsupportedOperationException();
  }

  @Override
  public AbstractState resolveState(String pCurFName, FormulaManager pManager, SSAMap pSsaMap) throws IOException {
    throw new UnsupportedOperationException();
  }

  @Override
  public SSAMap resolveOthers(DataInputStream pIn, FormulaManager pManager) throws IOException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public void serializeOthers(AbstractState pInputState, Collection<AbstractState> pOutputStates,
      DataOutputStream pOut, FormulaManager pManager) throws IOException {
    // TODO Auto-generated method stub

  }

}
