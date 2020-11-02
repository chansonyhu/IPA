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

import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;

public interface StoreHelper {
  public AbstractState getRealState(AbstractState pState);

  LocationState getLocationState(AbstractState pState);

  public String stateToString(AbstractState state, String funName);

  public void serializeState(AbstractState state, FormulaManager manager) throws IOException;

  public AbstractState resolveState(String curFName, FormulaManager manager) throws IOException;

  public AbstractState resolveState(String pCurFName, FormulaManager manager, SSAMap ssaMap) throws IOException;

  public AbstractState buildStateFromString(String curFName, String str);

  public AbstractState buildStateFromString(String curFName, String str, SSAMap ssaMap);

  public String getOthers(AbstractState inputState, Collection<AbstractState> outputStates);

  public SSAMap convertOthersToSSAMAP(String others);

  public SSAMap resolveOthers(DataInputStream in, FormulaManager manager) throws IOException;

  public void serializeOthers(AbstractState inputState, Collection<AbstractState> outputStates, DataOutputStream out, FormulaManager manager) throws IOException;

}
