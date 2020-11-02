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

import java.util.*;
import java.util.logging.Level;

import org.sosy_lab.common.Pair;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.blocks.Block;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.bam.BAMCEXSubgraphComputer;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.SmtInterpolEnvironment;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.SmtInterpolFormulaManager;

public class RefineHelper {
  private static RefineHelper instance;

  private List<Triple<AbstractState, Precision, Block>> curPrecisionFileCacheList = new ArrayList<>();
  private Map<AbstractState, Triple<AbstractState, Precision, Block>> curPrecisionFileCacheMap = new HashMap<>();
  private Map<ARGState, ARGState> backwardStateToStateMap = new HashMap<>();
  private Map<ARGState, ARGReachedSet> stateToReachedSetMap = new HashMap<>();
  private Map<AbstractState, AbstractState> replaceMap = new HashMap<>();

  private Map<ARGState, ARGState> newFlowBackwordStateToStateMap = new HashMap<>();
  private Map<ARGState, ARGReachedSet> newFlowStateToReachedSetMap = new HashMap<>();

  //public HashSet<ARGState> removedStates = new HashSet<>();
  public HashMap<ARGState, ArrayList<BAMCEXSubgraphComputer.BackwardARGState>> removedStates = new HashMap();
  public HashSet<BAMCEXSubgraphComputer.BackwardARGState> addedRemovedStateds = new HashSet<>();
  public HashMap<ARGState, Collection<ARGState>> removeChildStates = new HashMap<>();


  private boolean isRetFromMiddle = false;
  private boolean recover = false;
  public static boolean rerunning = false;
  public static int rerun_Leavenode = -1;
  public static boolean breakFromSuccessorAnalysis = false;
  public static boolean samePrecision = false;
  public static int sptimes = 0;
  public static int hole_counter = 0;
  public static boolean samePath = false;
  public static HashMap<Integer, Integer> pathCounter = new HashMap<>();

  public static HashSet<BooleanFormula> lazyBFCache = new HashSet<>();
  public static boolean isExpanding = false;
  public static int expansions = 0;

  //public static Vector<Triple<Triple<AbstractState, Precision, Block>, ARGReachedSet, ARGState>> holes = new Stack<>();
  public static Vector<ARGState> holes = new Stack<>();
  public static HashMap<ARGState, Vector<Triple<Triple<AbstractState, Precision, Block>, ARGReachedSet, ARGState>>> holes_content = new HashMap<>();

  public static int pathLens = 0;


  public static SmtInterpolEnvironment createEnvironment() {
    Configuration config = (Configuration) AutomaticCPAFactory.actualParameters[1];
    LogManager logger = (BasicLogManager) AutomaticCPAFactory.actualParameters[2];
    ShutdownNotifier shtdwn = (ShutdownNotifier) AutomaticCPAFactory.actualParameters[4];
    SmtInterpolEnvironment env = null;
    try {
      env = new SmtInterpolEnvironment(config, shtdwn, null, 42);
    } catch (InvalidConfigurationException e) {
      e.printStackTrace();
    }
    assert env != null;
    return env;
  }
  public boolean isfullPath(){
    //return holes.empty();
    return holes.isEmpty();
  }

  public void addHole(ARGState key, Triple value) {
    //holes.add(key);
    if(holes.contains(key)) {
      assert holes_content.containsKey(key);
      Vector<Triple<Triple<AbstractState, Precision, Block>, ARGReachedSet, ARGState>> content = holes_content.get(key);
      content.add(value);
      holes_content.put(key, content);
    } else {
      holes.add(key);
      Vector<Triple<Triple<AbstractState, Precision, Block>, ARGReachedSet, ARGState>> content = new Vector<>();
      content.add(value);
      holes_content.put(key,content);
    }

    System.out.println("Holes Size: " + holes.size());
    System.out.println("isfullPath: " + isfullPath());
  }

  public Pair<ARGState,Vector<Triple<Triple<AbstractState,Precision,Block>,ARGReachedSet,ARGState>>> getHole() {
    //assert !holes.empty() : "holes is empty";
    //return holes.pop();
    assert !holes.isEmpty() : "holes is empty";
    ARGState key = holes.remove(holes.size() - 1);
    return Pair.of(key, holes_content.remove(key));
  }


  public void setRecover(boolean p) {
    recover = p;
  }

  public boolean shouldRecover() {
    return recover;
  }

  public Map<ARGState, BAMCEXSubgraphComputer.BackwardARGState> getFinishedStates() {
    return finishedStates;
  }

  public NavigableSet<ARGState> getWaitList() {
    return waitlist;
  }

  public BAMCEXSubgraphComputer.BackwardARGState getRoot() {
    return root;
  }

  private Map<ARGState, BAMCEXSubgraphComputer.BackwardARGState> finishedStates;
  private NavigableSet<ARGState> waitlist;
  private BAMCEXSubgraphComputer.BackwardARGState root;

  public Map<ARGState, ARGState> getPathStateToReachedState() {
    return pathStateToReachedState;
  }

  public ARGReachedSet getReachedSet() {
    return reachedSet;
  }

  public BAMCEXSubgraphComputer.BackwardARGState getNewTreeTarget() {
    return newTreeTarget;
  }

  private Map<ARGState, ARGState> pathStateToReachedState;
  private ARGReachedSet reachedSet;
  private BAMCEXSubgraphComputer.BackwardARGState newTreeTarget;

  public ARGState getpCurrentState() {
    return currentState;
  }

  private ARGState currentState;

  private Set<ARGState> canRerun = new HashSet<>();

  private RefineHelper() {

  }

  public static RefineHelper getInstance() {
    if(instance == null) {
      instance = new RefineHelper();
    }
    return instance;
  }

  public static boolean isReusedFileCache(ReachedSet reachedSet) {
    //the depth is two
    ARGState firstState = (ARGState)reachedSet.getFirstState();
    Collection<ARGState> childsState = firstState.getChildren();
    for(ARGState curState : childsState) {
      if(curState.getChildren().size() > 0) {
        return false;
      }
    }

    if(OneFileStore.getCfaNode((ARGState)reachedSet.getFirstState()) instanceof FunctionEntryNode) {
      if(OneFileStore.getCfaNode((ARGState)reachedSet.getLastState()) instanceof FunctionExitNode) {
        return true;
      }
    }
    return false;
  }

  public void buildCurPrecisionFileCacheMap() {
    for(Triple<AbstractState, Precision, Block> curTriple : curPrecisionFileCacheList) {
      AbstractState inputState = curTriple.getFirst();
      Collection<ARGState> childStates = ((ARGState)inputState).getChildren();
      for(ARGState curState : childStates) {
        curPrecisionFileCacheMap.put(curState, curTriple);
      }
    }
  }

  public void saveTheScene(BAMCEXSubgraphComputer.BackwardARGState pRoot, NavigableSet<ARGState> pWaitList,
                           Map<ARGState, BAMCEXSubgraphComputer.BackwardARGState> pFinishedStates,
                           Map<ARGState, ARGState> pPathStateToReachedState, ARGReachedSet pReachedSet,
                           BAMCEXSubgraphComputer.BackwardARGState pNewTreeTarget, ARGState pCurrentState) {
    root = pRoot;
    waitlist = pWaitList;
    finishedStates = pFinishedStates;
    pathStateToReachedState = new HashMap<>();
    BAMCEXSubgraphComputer.BackwardARGState key;
    for(ARGState value : pPathStateToReachedState.values()) {
      key = new BAMCEXSubgraphComputer.BackwardARGState(value);
      pathStateToReachedState.put(key, value);
    }
    //pathStateToReachedState = pPathStateToReachedState;
    reachedSet = pReachedSet;
    newTreeTarget = pNewTreeTarget;
    currentState = pCurrentState;
  }

  public void clearAll() {
    curPrecisionFileCacheList.clear();
    curPrecisionFileCacheMap.clear();
    backwardStateToStateMap.clear();
    stateToReachedSetMap.clear();
    replaceMap.clear();
//    canRerun.clear();
  }


  public List<Triple<AbstractState, Precision, Block>> getCurPrecisionFileCacheList() {
    return curPrecisionFileCacheList;
  }


  public void setCurPrecisionFileCacheList(List<Triple<AbstractState, Precision, Block>> pCurPrecisionFileCacheList) {
    curPrecisionFileCacheList = pCurPrecisionFileCacheList;
  }


  public Map<AbstractState, Triple<AbstractState, Precision, Block>> getCurPrecisionFileCacheMap() {
    return curPrecisionFileCacheMap;
  }


  public void setCurPrecisionFileCacheMap(
      Map<AbstractState, Triple<AbstractState, Precision, Block>> pCurPrecisionFileCacheMap) {
    curPrecisionFileCacheMap = pCurPrecisionFileCacheMap;
  }


  public Map<ARGState, ARGState> getBackwardStateToStateMap() {
    return backwardStateToStateMap;
  }


  public void setBackwardStateToStateMap(Map<ARGState, ARGState> pBackwardStateToStateMap) {
    backwardStateToStateMap = pBackwardStateToStateMap;
  }


  public Map<ARGState, ARGReachedSet> getStateToReachedSetMap() {
    return stateToReachedSetMap;
  }


  public void setStateToReachedSetMap(Map<ARGState, ARGReachedSet> pStateToReachedSetMap) {
    stateToReachedSetMap = pStateToReachedSetMap;
  }


  public Map<AbstractState, AbstractState> getReplaceMap() {
    return replaceMap;
  }


  public void setReplaceMap(Map<AbstractState, AbstractState> pReplaceMap) {
    replaceMap = pReplaceMap;
  }


  public boolean isRetFromMiddle() {
    return isRetFromMiddle;
  }


  public void setRetFromMiddle(boolean pIsRetFromMiddle) {
    CPAMain.logManager.log(Level.INFO,"set RFM to " + pIsRetFromMiddle);
    isRetFromMiddle = pIsRetFromMiddle;
  }


  public Map<ARGState, ARGState> getNewFlowBackwordStateToStateMap() {
    return newFlowBackwordStateToStateMap;
  }


  public void setNewFlowBackwordStateToStateMap(Map<ARGState, ARGState> pNewFlowBackwordStateToStateMap) {
    newFlowBackwordStateToStateMap = pNewFlowBackwordStateToStateMap;
  }


  public Map<ARGState, ARGReachedSet> getNewFlowStateToReachedSetMap() {
    return newFlowStateToReachedSetMap;
  }


  public void setNewFlowStateToReachedSetMap(Map<ARGState, ARGReachedSet> pNewFlowStateToReachedSetMap) {
    newFlowStateToReachedSetMap = pNewFlowStateToReachedSetMap;
  }


  public Set<ARGState> getCanRerun() {
    return canRerun;
  }


  public void setCanRerun(Set<ARGState> pCanRerun) {
    canRerun = pCanRerun;
  }

}
