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

import java.util.HashSet;
import java.util.Set;

import org.sosy_lab.cpachecker.core.defaults.VariableTrackingPrecision;
import org.sosy_lab.cpachecker.core.defaults.VariableTrackingPrecision.ScopedRefinablePrecision;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.ProgramInfo;
import org.sosy_lab.cpachecker.util.Precisions;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

import com.google.common.collect.ImmutableSortedSet;

public class ValueAnalysisPrecisionExtractor implements PrecisionExtractor {
  private static final String totalPrecision = "PREB\nTOTAL\nPREE\n";

  @Override
  public String getPrecisionString(Precision precision, String funName) {
    ScopedRefinablePrecision scopedRefinablePrecision = Precisions.extractPrecisionByType(precision, ScopedRefinablePrecision.class);
    if(scopedRefinablePrecision == null) {
      return totalPrecision;
    }
    return scopedRefinablePrecision.toFileString(ProgramInfo.getInstance().getRelativeFunMap(funName));
  }

  @Override
  public Set<PrecisionHelpState> getNewestPrecision(UnmodifiableReachedSet pReached) {
    VariableTrackingPrecision consolidatedPrecision =
        VariableTrackingPrecision.joinVariableTrackingPrecisionsInReachedSet((ReachedSet)pReached);
    ScopedRefinablePrecision scopedRefinablePrecision = Precisions.extractPrecisionByType(consolidatedPrecision, ScopedRefinablePrecision.class);
    if(scopedRefinablePrecision == null) {
      return new HashSet<>();
    }
    ImmutableSortedSet<MemoryLocation> rawPrecision = scopedRefinablePrecision.getRawPrecision();
    Set<PrecisionHelpState> ans = new HashSet<>();

    Set<String> functions = new HashSet<>();
    for(MemoryLocation variable : rawPrecision) {
      if(variable.isOnFunctionStack()) {
        functions.add(variable.getFunctionName());
      }
    }
    for(String name : functions) {
      ans.add(new PrecisionHelpState(name, scopedRefinablePrecision, this));
    }
    return ans;
  }
}
