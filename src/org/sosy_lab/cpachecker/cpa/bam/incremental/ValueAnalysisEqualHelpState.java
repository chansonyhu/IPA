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

import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.cpa.value.type.Value;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

public class ValueAnalysisEqualHelpState extends EqualHelpState {
  private PersistentMap<MemoryLocation, Value> constantsMap;
  private long nonce;

  public ValueAnalysisEqualHelpState(ValueAnalysisState state, String funName) {
    this.constantsMap = state.getConstantsMap1();
    nonce = System.currentTimeMillis();
  }

  @Override
  public int hashCode() {
    return constantsMap.hashCode();
  }

  @Override
  public boolean equals(Object other) {
    if(other == this) {
      return true;
    }
    if(!(other instanceof ValueAnalysisEqualHelpState)) {
      return false;
    }
    return constantsMap.equals(((ValueAnalysisEqualHelpState)other).constantsMap);// &&
            //nonce == ((ValueAnalysisEqualHelpState)other).nonce;
  }

  public PersistentMap<MemoryLocation, Value> getConstantsMap() {
    return constantsMap;
  }

  public void setConstantsMap(PersistentMap<MemoryLocation, Value> pConstantsMap) {
    constantsMap = pConstantsMap;
  }

}
