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

import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;

public class PredicateAnalysisEqualHelpState extends EqualHelpState {
  public static Timer buildEqualHelpStateTimer = new Timer();
  private BooleanFormula formula;
  private Region region;
  private long nonce;
  public PredicateAnalysisEqualHelpState(PredicateAbstractState state, String funName) throws IllegalArgumentException {
//    buildEqualHelpStateTimer.start();
    this.formula = state.getAbstractionFormula().asFormula();
    AbstractionManager abstractionManager = GlobalInfo.getInstance().getAbstractionManager();
    region = abstractionManager.buildRegionFromFormula(formula);
    nonce = System.currentTimeMillis();
//    buildEqualHelpStateTimer.stop();
  }

  @Override
  public int hashCode() {
    return region.hashCode();
  }

  @Override
  public boolean equals(Object obj) {
    if(obj == this) {
      return true;
    }
    if(!(obj instanceof PredicateAnalysisEqualHelpState)) {
      return false;
    }
    return region.equals(((PredicateAnalysisEqualHelpState)obj).region);// &&
            //nonce == ((PredicateAnalysisEqualHelpState)obj).nonce;
  }

  public BooleanFormula getFormula() {
    return formula;
  }

  public void setFormula(BooleanFormula pFormula) {
    formula = pFormula;
  }
}
