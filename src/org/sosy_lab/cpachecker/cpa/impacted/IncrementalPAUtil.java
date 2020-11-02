/*
 * CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.cpachecker.cpa.impacted;

import com.google.common.collect.Maps;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.cpachecker.cfa.ast.c.CDummyDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CSimpleDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.defaults.SingletonPrecision;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.waitlist.ReversePostorderSortedWaitlist;
import org.sosy_lab.cpachecker.core.waitlist.Waitlist;
import org.sosy_lab.cpachecker.core.waitlist.Waitlist.WaitlistFactory;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.composite.CompositePrecision;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.pcc.strategy.PartitionedReachedSetStrategy;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;

@Options(prefix="cpa.incremental.pa")
public class IncrementalPAUtil {
  private static IncrementalPAUtil instance;
  public int numOfBot = 0;
  public boolean isInvMiss = false;
  public ArrayList<Triple<AbstractState, Precision, Integer>> waitSet = new ArrayList<>();
  public ReachedSet reached;
  public int absStop = 0;
  public int nonAbsStop = 0;
  // ipa: isInit为true表示被annotation初始化了reachedSet
  public static boolean isInit = true;
  public Map<CFANode, Region> regions = Maps.newHashMap();
  // ipa: curTarget = 100 代表该状态是重用的不变式； curTarget = -1 代表该状态是当前计算出来的
  public int curTarget = -1;
  public int coverage_check = 0;
  public boolean curNonAbsStop = false;
  public int prevLoc = -1;

  public final CSimpleDeclaration dummyVariable = new CDummyDeclaration();

  private IncrementalPAUtil(Configuration pConfig) {

    try {
      pConfig.inject(this, IncrementalPAUtil.class);
    } catch (InvalidConfigurationException e) {
      e.printStackTrace();
    }

  }

  public ReachedSet setReached(ReachedSet pReached) {
    //reached = new PartitionedReachedSetStrategy(pReached);
    CompositePrecision cp;
    List<Precision> wrappedPrecision = new ArrayList<>();
    wrappedPrecision.add(SingletonPrecision.getInstance());
    wrappedPrecision.add(SingletonPrecision.getInstance());
    wrappedPrecision.add(SingletonPrecision.getInstance());
    wrappedPrecision.add(ImpactedHelper.getInstance().bestPrecisionPerFunction);
    wrappedPrecision.add(SingletonPrecision.getInstance());
    wrappedPrecision.add(SingletonPrecision.getInstance());
    cp = new CompositePrecision(wrappedPrecision);

    reached = ImpactedHelper.getInstance().factory.createReachedSet();
    int absCount = 0;
    for(Triple<AbstractState, Precision, Integer> tri : waitSet) {
      try {
        AbstractionFormula absF = AbstractStates.extractStateByType(((ARGState)tri.getFirst()),
            PredicateAbstractState.class).getAbstractionFormula();
        if(absF.isFalse()) {
          throw new UnsupportedOperationException("Wrong formula");
        }
        ((ARGState) tri.getFirst()).target = 100;
//        reached.add(tri.getFirst(), tri.getSecond());
        reached.add(tri.getFirst(), cp);
        if(AbstractStates.extractStateByType(tri.getFirst(), PredicateAbstractState.class).isAbstractionState()) {
          absCount+=1;
        }
      } catch (IllegalArgumentException iae) {
        continue;
      }
    }
    for(AbstractState s : reached) {
      if(!AbstractStates.extractStateByType(s, PredicateAbstractState.class).isAbstractionState()) {
        reached.removeOnlyFromWaitlist(s);
      } else {
        boolean complete = isComplete((ARGState) s);
        if(complete) {
          reached.removeOnlyFromWaitlist(s);
        }
      }
    }
    pReached = reached;
    // System.out.println("initial waitlist (after):" + reached.getWaitlist().size());
    return pReached;
  }

  private boolean isComplete(ARGState s) {
    ARGState current = s;
    Waitlist.TraversalMethod traversalMethod = Waitlist.TraversalMethod.BFS;
    WaitlistFactory waitlistFactory = ReversePostorderSortedWaitlist.factory(traversalMethod);
    Waitlist waitlist = waitlistFactory.createWaitlistInstance();
    for(AbstractState tmp : current.getChildren()) {
      waitlist.add(tmp);
    }
    // boolean isPartial = false;
    while(waitlist.size() > 0) {
      ARGState state = (ARGState) waitlist.pop();
      if(AbstractStates.extractStateByType(state, PredicateAbstractState.class).isAbstractionState()) {
        // System.out.println(state.toString());
        if(waitlist.isEmpty()) {
          return true;
        } else {
          // isPartial = true;
          continue;
        }
      }
      for(AbstractState tmp : state.getChildren()) {
        waitlist.add(tmp);
      }
    }
    return false;
  }

  public void setReached1(final ReachedSet pReached) {
    reached = pReached;

    for(Triple<AbstractState, Precision, Integer> tri : waitSet) {
      try {
        reached.reAddToWaitlist(tri.getFirst());
      } catch (IllegalArgumentException iae) {
        continue;
      }
    }
  }

  public static IncrementalPAUtil getInstance() {
    if(instance == null) {
      instance = new IncrementalPAUtil(CPAMain.cpaConfig);
    }
    return instance;
  }
}
