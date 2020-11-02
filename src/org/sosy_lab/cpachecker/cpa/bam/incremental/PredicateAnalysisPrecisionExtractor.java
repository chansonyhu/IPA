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

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSetMultimap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.util.Precisions;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;

import com.google.common.collect.ImmutableSet;

public class PredicateAnalysisPrecisionExtractor implements PrecisionExtractor {
  @Override
  public String getPrecisionString(Precision precision, String funName) {
    PredicatePrecision predicatePrecision = Precisions.extractPrecisionByType(precision, PredicatePrecision.class);
    Set<AbstractionPredicate> tmpPredicates = predicatePrecision.getFunctionPredicates().get(funName);
    HashSet<AbstractionPredicate> functionPredicates = new HashSet<>();
    functionPredicates.addAll(tmpPredicates);
    //TODO qianshan.
    if(functionPredicates.size() == 0) {
      ImmutableMap predMap = ((ImmutableSetMultimap) predicatePrecision.getLocalPredicates()).asMap();
      Iterator iter = predMap.keySet().iterator();
      while(iter.hasNext()){
        CFANode fn = (CFANode) iter.next();
        if(fn instanceof FunctionEntryNode || fn instanceof FunctionExitNode) {
          functionPredicates.addAll((ImmutableSet)predMap.get(fn));
        }
      }
    }
    List<String> predicateList = new ArrayList<>();
    for(AbstractionPredicate curPredicate : functionPredicates) {
      String curPStr = translatePredicateToString(curPredicate);
      predicateList.add(curPStr);
    }

    //must sort
    Collections.sort(predicateList);
    StringBuilder builder = new StringBuilder();
    builder.append(PRECISIONBEGIN);
    for(int i = 0; i < predicateList.size(); i++) {
      builder.append(predicateList.get(i));
      if(i != predicateList.size() - 1) {
        builder.append(",");
      }
    }
    if(builder.length() != PRECISIONBEGIN.length()) {
      builder.append("\n");
    }
    builder.append(PRECISIONEND);
    return builder.toString();
  }

  private String translatePredicateToString(AbstractionPredicate abstractionPredicate) {
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
    BooleanFormula symbolicAtom = abstractionPredicate.getSymbolicAtom();
    return formulaManagerView.dumpFormula(symbolicAtom).toString();
  }

  public List<BooleanFormula> extractPrecision(Precision precision, String funName) {
    List<BooleanFormula> ans = new ArrayList<>();
    PredicatePrecision predicatePrecision = Precisions.extractPrecisionByType(precision, PredicatePrecision.class);
    Set<AbstractionPredicate> functionPredicates = predicatePrecision.getFunctionPredicates().get(funName);
    for(AbstractionPredicate curPredicate : functionPredicates) {
      ans.add(curPredicate.getSymbolicAtom());
    }
    return ans;
  }


  @Override
  public Set<PrecisionHelpState> getNewestPrecision(UnmodifiableReachedSet reached) {
    Set<Precision> seenPrecisions = Collections.newSetFromMap(new IdentityHashMap<Precision, Boolean>());
    for(Precision precision : reached.getPrecisions()) {
      seenPrecisions.add(precision);
    }

    Set<PrecisionHelpState> newestPrecisions = new HashSet<>();
    for (Precision curP : seenPrecisions) {
      PredicatePrecision preds = Precisions.extractPrecisionByType(curP, PredicatePrecision.class);
      if (preds != null) {
        for (Entry<String, Collection<AbstractionPredicate>> curEntry : preds.getFunctionPredicates().asMap()
            .entrySet()) {
          String funName = curEntry.getKey();
          newestPrecisions.add(new PrecisionHelpState(funName, curP, this));
        }
      }
    }
    return newestPrecisions;
  }

}
