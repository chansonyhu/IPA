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

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.defaults.SingletonPrecision;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.composite.CompositePrecision;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Multimap;

public class PrecisionHelpState implements Serializable {
  private String funName;
  private Precision precision;
  private List<String> precisionStrs;
  private String helpStr;

  public PrecisionHelpState(String funName, Precision precision, PrecisionExtractor pExtractor) {
    this.funName = funName;
    this.precision = precision;
    this.helpStr = funName + IncrementalCache.FUNCTIONNAMEPRECISIONSPLIT + pExtractor.getPrecisionString(precision, funName);
  }

  public PrecisionHelpState(String funName, List<BooleanFormula> formulas, PrecisionExtractor pExtractor) {
    this.funName = funName;
    this.precision = buildPrecision(funName, formulas);
    this.helpStr = funName + IncrementalCache.FUNCTIONNAMEPRECISIONSPLIT + pExtractor.getPrecisionString(this.precision, funName);
  }

  public PrecisionHelpState(String funName, String precisionStr) {
    this.funName = funName;
    if(CPAMain.isUesTextSummary) {
      this.helpStr = funName + IncrementalCache.FUNCTIONNAMEPRECISIONSPLIT + PrecisionExtractor.PRECISIONBEGIN + precisionStr + PrecisionExtractor.PRECISIONEND;
      return;
    }
    List<String> tmpList = new ArrayList<>();
    for(String tmpS : precisionStr.split(",")) {
      tmpList.add(tmpS);
    }
    Collections.sort(tmpList);
    StringBuilder pBuilder = new StringBuilder();
    for(int i = 0; i < tmpList.size(); i++) {
      pBuilder.append(tmpList.get(i));
      if(i != tmpList.size() - 1) {
        pBuilder.append(',');
      }
    }
    if(tmpList.size() > 1) {
      pBuilder.append("\n");
    }
    this.precisionStrs = tmpList;
    this.helpStr = funName + IncrementalCache.FUNCTIONNAMEPRECISIONSPLIT + PrecisionExtractor.PRECISIONBEGIN + pBuilder.toString() + PrecisionExtractor.PRECISIONEND;
  }

  @Override
  public int hashCode() {
    return this.helpStr.hashCode();
  }

  @Override
  public boolean equals(Object other) {
    if(!(other instanceof PrecisionHelpState)) {
      return false;
    }
    PrecisionHelpState otherHelpState = (PrecisionHelpState)other;
    boolean equals = this.helpStr.equals(otherHelpState.helpStr);
    if(equals) {
      if (this.precision == null) {
        this.precision = otherHelpState.precision;
      }
    }
    return equals;
  }

  @Override
  public String toString() {
    return this.helpStr;
  }

  public String getFunName() {
    return funName;
  }

  public Precision getPrecision() {
    if(precision == null) {
      FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
      List<BooleanFormula> formulas = new ArrayList<>(this.precisionStrs.size());
      for(String curS : this.precisionStrs) {
        if(curS.trim().equals("")) {
          continue;
        }
        BooleanFormula formula = formulaManagerView.parse(curS);
        formulas.add(formula);
      }
      this.precision = buildPrecision(this.funName, formulas);
    }
    return precision;
  }

  public String getHelpStr() {
    return helpStr;
  }

  private Precision buildPrecision(String funName, List<BooleanFormula> formulas) {
    List<Precision> precisions = new ArrayList<Precision>(5);
    SingletonPrecision singletonPrecision = SingletonPrecision.getInstance();
    precisions.add(singletonPrecision);
    precisions.add(singletonPrecision);
    precisions.add(singletonPrecision);

    PredicatePrecision predicatePrecision = PredicatePrecision.empty();
    Multimap<String, AbstractionPredicate> newPredicates = ArrayListMultimap.create();
    AbstractionManager abstractionManager = GlobalInfo.getInstance().getAbstractionManager();
    for(BooleanFormula formula : formulas) {
      AbstractionPredicate abstractionPredicate = abstractionManager.makePredicate(formula);
      newPredicates.put(funName, abstractionPredicate);
    }
    predicatePrecision.addFunctionPredicates(newPredicates);
    precisions.add(predicatePrecision);

    precisions.add(singletonPrecision);
    CompositePrecision compositePrecision = new CompositePrecision(precisions);
    return compositePrecision;
  }

}
