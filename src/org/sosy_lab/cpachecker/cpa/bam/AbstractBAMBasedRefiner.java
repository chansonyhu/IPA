/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
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
package org.sosy_lab.cpachecker.cpa.bam;

import java.io.IOException;
import java.io.Writer;
import java.util.*;
import java.util.logging.Level;

import com.google.common.base.Predicate;
import com.google.common.base.Predicates;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.Files;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.Paths;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cfa.blocks.Block;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionSummaryEdge;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.CounterexampleInfo;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.*;
import org.sosy_lab.cpachecker.cpa.bam.BAMCEXSubgraphComputer.BackwardARGState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.LazyARGToDotWriter;
import org.sosy_lab.cpachecker.cpa.bam.incremental.RefineHelper;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;

import com.google.errorprone.annotations.ForOverride;

import static org.sosy_lab.cpachecker.util.AbstractStates.extractLocation;

/**
 * This is an extension of {@link AbstractARGBasedRefiner} that takes care of
 * flattening the ARG before calling {@link #performRefinement0(ARGReachedSet, MutableARGPath)}.
 *
 * Warning: Although the ARG is flattened at this point, the elements in it have
 * not been expanded due to performance reasons.
 */
@Options(prefix="cpa.arg")
public abstract class AbstractBAMBasedRefiner extends AbstractARGBasedRefiner {

  final Timer computePathTimer = new Timer();
  final Timer computeSubtreeTimer = new Timer();
  final Timer computeCounterexampleTimer = new Timer();

  @Option(secure=true, description="export used parts of blocked ARG as .dot file (lazy)")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  private Path lazySimplifiedArgFile = null;
  private int expandTimes = 0;
  private boolean isFirstHole = true;

  private final BAMTransferRelation transfer;
  private final BAMCPA bamCpa;
  private final Map<ARGState, ARGState> subgraphStatesToReachedState = new HashMap<>();
  private ARGState rootOfSubgraph = null;

  final static BackwardARGState DUMMY_STATE_FOR_MISSING_BLOCK = new BackwardARGState(new ARGState(null, null));

  protected AbstractBAMBasedRefiner(ConfigurableProgramAnalysis pCpa)
      throws InvalidConfigurationException {
    super(pCpa);

    bamCpa = (BAMCPA)pCpa;
    transfer = bamCpa.getTransferRelation();
    bamCpa.getStatistics().addRefiner(this);
  }

  /**
   * When inheriting from this class, implement this method instead of
   * {@link #performRefinement(ReachedSet)}.
   */
  @ForOverride
  protected abstract CounterexampleInfo performRefinement0(ARGReachedSet pReached, ARGPath pPath) throws CPAException, InterruptedException;

  @Override
  protected final CounterexampleInfo performRefinement(ARGReachedSet pReached, ARGPath pPath) throws CPAException, InterruptedException {
    assert pPath == null || pPath.size() > 0;

    if (pPath == null) {
      // The counter-example-path could not be constructed, because of missing blocks (aka "holes").
      // We directly return SPURIOUS and let the CPA-algorithm run again.
      // During the counter-example-path-building we already re-added the start-states of all blocks,
      // that lead to the missing block, to the waitlists of those blocks.
      // Thus missing blocks are analyzed and rebuild again in the next CPA-algorithm.
      return CounterexampleInfo.spurious();
    } else {
      return performRefinement0(new BAMReachedSet(transfer, pReached, pPath, subgraphStatesToReachedState, rootOfSubgraph), pPath);
    }
  }

  @Override
  protected final ARGPath expandPath(ARGPath pPath, Pair<ARGState,Vector<Triple<Triple<AbstractState,Precision,Block>,ARGReachedSet,ARGState>>> holeSig)throws InterruptedException, CPATransferException {
    if(pPath == null) return pPath;
    ARGReachedSet reachedSet = null;
    Vector holeSet = holeSig.getSecond();
    ARGState reducedOut = holeSig.getFirst();
    ArrayList<BAMCEXSubgraphComputer.BackwardARGState> backExpandedOuts = null;
    boolean firstGetbackExpandedOuts = true;

    isFirstHole = true;
    while(!holeSet.isEmpty()) {
      Triple hole = (Triple) holeSet.remove(holeSet.size() - 1);
      Triple<AbstractState, Precision, Block> curTriple = (Triple) hole.getFirst();
      reachedSet = (ARGReachedSet) hole.getSecond();
      ARGState currentState = (ARGState) hole.getThird();
      if(isFirstHole) {
        lazySimplifiedArgFile = Paths.get("./output/lazyExpansion/ExpandedBlockedARGSimplified" + expandTimes++ + ".dot");
        //TODO qianshan we do not need to export dot file for now
        //exportUsedReachedSets(lazySimplifiedArgFile, reachedSet.asReachedSet());
        isFirstHole = false;
      }

      try {
        if(!RefineHelper.getInstance().removedStates.containsKey(reducedOut))
          return pPath;
        //TODO Oct 19, rerun reduce后相同hole
        int flag = transfer.bamcexSubgraphComputer.rerunFileCachedFun(curTriple, reachedSet,
            currentState);//TODO a bfs strategy find the error trace according to function's inner structure
        if(flag == 1)
          return pPath;
      } catch (CPAException | InterruptedException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      if(firstGetbackExpandedOuts) {
        backExpandedOuts = RefineHelper.getInstance().removedStates.remove(reducedOut);
        firstGetbackExpandedOuts = false;
      }
      //TODO Oct 19, 145-156得到所有的BackExpandedOut
      assert RefineHelper.getInstance().getReplaceMap().containsKey(currentState);
      BackwardARGState pivot = backExpandedOuts.remove(backExpandedOuts.size() - 1);
      assert holeSet.size() == backExpandedOuts.size() : "Incompatible size!";
      AbstractState replaceState = RefineHelper.getInstance().getReplaceMap().get(currentState);
      if(!RefineHelper.getInstance().getReplaceMap().containsKey(currentState)) {
          //return pPath;
          throw new AssertionError();
      }
      currentState = (ARGState) replaceState;
      RefineHelper.getInstance().getCurPrecisionFileCacheMap().remove(currentState);
      if(currentState == null) {
        //return pPath;
        throw new AssertionError();
      }
      BackwardARGState newCurrentState = new BackwardARGState(currentState);
      pivot.replaceInARGWith(newCurrentState);
      //for(BackwardARGState back : pivot.getParents()) {
      //  newCurrentState.addParent(back);
      //}
      transfer.bamcexSubgraphComputer.pathStateToReachedState.put(newCurrentState, currentState);
      transfer.bamcexSubgraphComputer.pathStateToReachedState.remove(pivot);

      if (CPAMain.isReuseSummary) {  //&& CPAMain.noLazyExpansion
        if (RefineHelper.getInstance().getCurPrecisionFileCacheMap().containsKey(currentState)) {
          RefineHelper.getInstance().getBackwardStateToStateMap().put(newCurrentState, currentState);
          RefineHelper.getInstance().getStateToReachedSetMap().put(currentState, reachedSet);
        }
      }

      // add parent for further processing
      final ARGState child = currentState;
      assert currentState.getParents().size() == 1 : "The summary block has more than one entries";
      currentState = (ARGState) currentState.getParents().toArray()[0];
      //for (final ARGState child : currentState) {

      //final BackwardARGState newChild = new BackwardARGState(child);
      final BackwardARGState newChild = newCurrentState;

      if (transfer.bamcexSubgraphComputer.expandedToReducedCache.containsKey(child)) {
        // If child-state is an expanded state, we are at the exit-location of a block.
        // In this case, we enter the block (backwards).
        // We must use a cached reachedSet to process further, because the block has its own reachedSet.
        // The returned 'innerTree' is the rootNode of the subtree, created from the cached reachedSet.
        // The current subtree (successors of child) is appended beyond the innerTree, to get a complete subgraph.
        final ARGState reducedTarget = (ARGState) transfer.bamcexSubgraphComputer.expandedToReducedCache.get(child);
        BackwardARGState innerTree = transfer.bamcexSubgraphComputer.computeCounterexampleSubgraphForBlock(currentState, reducedTarget, newChild);
        assert innerTree != DUMMY_STATE_FOR_MISSING_BLOCK : "Dummy State";
        //TODO Oct 19, SubgraphForBlock一次，把多个BackExpandedIn都与之链接
        BackwardARGState old = RefineHelper.getInstance().removedStates.get(currentState).get(0);
        //old.replaceInARGWith(innerTree);
        innerTree.childrenAddParentTo(old);
        innerTree.childrenDelParentTo(innerTree);
        //innerTree.replaceInARGWith(old, true);

        // reconnect ARG
        //for (ARGState outerChild : newCurrentState.getChildren()) {
        //  outerChild.addParent(newChild);
        //}
        //TODO delete redundant child state of BackExpandedIn
        BackwardARGState expandedOut = (BackwardARGState) (old.getChildren().toArray()[0]);
        assert extractLocation(expandedOut).getNodeNumber() == extractLocation(old).getNodeNumber() - 1 : "This is not an exit child.";
        //TODO Oct 19, old.removeChild(expandedOut)
        old.removeChild(expandedOut);
        //expandedOut.removeFromARG();
        //newCurrentState.removeFromARG();

        //assert transfer.bamcexSubgraphComputer.pathStateToReachedState.containsKey(newCurrentState) : "root of subgraph was not finished";
        //transfer.bamcexSubgraphComputer.pathStateToReachedState.remove(expandedOut); // not needed any more

        // now the complete inner tree (including all successors of the state innerTree on paths to reducedTarget)
        // is inserted between newCurrentState and child.

        assert transfer.bamcexSubgraphComputer.pathStateToReachedState.containsKey(newChild) : "end of subgraph was not handled";
        assert transfer.bamcexSubgraphComputer.pathStateToReachedState.get(old) == currentState : "input-state must be from outer reachedset";

        // check that at block output locations the first reached state is used for the CEXsubgraph,
        // i.e. the reduced abstract state from the (most) inner block's reached set.
        ARGState matchingChild = (ARGState) transfer.bamcexSubgraphComputer.expandedToReducedCache.get(child);
        while (transfer.bamcexSubgraphComputer.expandedToReducedCache.containsKey(matchingChild)) {
          matchingChild = (ARGState) transfer.bamcexSubgraphComputer.expandedToReducedCache.get(matchingChild);
        }
        assert transfer.bamcexSubgraphComputer.pathStateToReachedState.get(newChild) == matchingChild : "output-state must be from (most) inner reachedset";




        //for(BackwardARGState back : pivot.getParents()) {
        //  newCurrentState.addParent(back);
        //}
      } else {
        // child is a normal successor
        // -> create an simple connection from parent to current
        assert currentState.getEdgeToChild(child) != null : "unexpected ARG state: parent has no edge to child.";
        newChild.addParent(newCurrentState);


        transfer.bamcexSubgraphComputer.pathStateToReachedState.put(newCurrentState, currentState);
        transfer.bamcexSubgraphComputer.pathStateToReachedState.remove(pivot);


      }
      //hole = (Triple) holeSet.remove(holeSet.size() - 1);
      //curTriple = (Triple) hole.getFirst();
      //reachedSet = (ARGReachedSet) hole.getSecond();
      //currentState = (ARGState) hole.getThird();
    }
    //}

    /*for (final ARGState child : currentState.getChildren()) {
      final BackwardARGState newChild = finishedStates.get(child);
      assert currentState.getEdgeToChild(child) != null: "unexpected ARG state: parent has no edge to child.";
      newChild.addParent(newCurrentState);
    }*/

    lazySimplifiedArgFile =  Paths.get("./output/lazyExpansion/ExpandedBlockedARGSimplified" + expandTimes++ + ".dot");
    assert reachedSet != null : "cannot export used reached sets in expandPath()";
    //TODO qianshan we do not need to export dot file for now
    //exportUsedReachedSets(lazySimplifiedArgFile, reachedSet.asReachedSet());
    return ARGUtils.getRandomPath(pPath.getFirstState());
  }

    @Override
  protected final ARGPath computePath(ARGState pLastElement, ARGReachedSet pReachedSet) throws InterruptedException, CPATransferException {
    assert pLastElement.isTarget();
    assert pReachedSet.asReachedSet().contains(pLastElement) : "targetState must be in mainReachedSet.";

    subgraphStatesToReachedState.clear();

    computePathTimer.start();
    try {
      computeSubtreeTimer.start();
      try {
        rootOfSubgraph = transfer.computeCounterexampleSubgraph(pLastElement, pReachedSet, subgraphStatesToReachedState);
        if (rootOfSubgraph == DUMMY_STATE_FOR_MISSING_BLOCK) {
          return null;
        }
      } finally {
        computeSubtreeTimer.stop();
      }

      //changed by cailiming
      if(RefineHelper.getInstance().isRetFromMiddle()) {
        ARGState childState = (ARGState) rootOfSubgraph.getChildren().toArray()[0];
        rootOfSubgraph.removeFromARG();
        rootOfSubgraph = childState;
      }

      computeCounterexampleTimer.start();
      try {
        // We assume, that every path in the subgraph reaches the target state. Thus we choose randomly.
        return ARGUtils.getRandomPath(rootOfSubgraph);
      } finally {
        computeCounterexampleTimer.stop();
      }
    } finally {
      computePathTimer.stop();
    }
  }

  private void exportUsedReachedSets(final Path superArgFile, final UnmodifiableReachedSet  mainReachedSet) {

    if (superArgFile != null) {

      final Multimap<ARGState, ARGState> connections = HashMultimap.create();
      final Set<ARGState> rootStates = getUsedRootStates(mainReachedSet, connections);
      writeArg(superArgFile, connections, rootStates);
    }
  }



  private Set<ARGState> getUsedRootStates(final UnmodifiableReachedSet  mainReachedSet,
                                          final Multimap<ARGState, ARGState> connections) {
    final Set<UnmodifiableReachedSet > finished = new HashSet<>();
    final Deque<UnmodifiableReachedSet > waitlist = new ArrayDeque<>();
    waitlist.add(mainReachedSet);
    while (!waitlist.isEmpty()){
      final UnmodifiableReachedSet  reachedSet = waitlist.pop();
      if (!finished.add(reachedSet)) {
        continue;
      }
      final ARGState rootState = (ARGState) reachedSet.getFirstState();
      final Set<UnmodifiableReachedSet > referencedReachedSets = getConnections(rootState, connections);
      waitlist.addAll(referencedReachedSets);
    }

    final Set<ARGState> rootStates = new HashSet<>();
    for (UnmodifiableReachedSet  reachedSet : finished) {
      rootStates.add((ARGState)reachedSet.getFirstState());
    }
    return rootStates;
  }

  private Set<UnmodifiableReachedSet > getConnections(final ARGState rootState, final Multimap<ARGState, ARGState> connections) {
    final Set<UnmodifiableReachedSet > referencedReachedSets = new HashSet<>();
    final Set<ARGState> finished = new HashSet<>();
    final Deque<ARGState> waitlist = new ArrayDeque<>();
    waitlist.add(rootState);
    while (!waitlist.isEmpty()) {
      ARGState state = waitlist.pop();
      if (!finished.add(state)) {
        continue;
      }
      if (transfer.abstractStateToReachedSet.containsKey(state)) {
        UnmodifiableReachedSet  target = transfer.abstractStateToReachedSet.get(state);
        referencedReachedSets.add(target);
        ARGState targetState = (ARGState) target.getFirstState();
        connections.put(state, targetState);
      }
      if (transfer.expandedToReducedCache.containsKey(state)) {
        AbstractState sourceState = transfer.expandedToReducedCache.get(state);
        connections.put((ARGState) sourceState, state);
      }
      waitlist.addAll(state.getChildren());
    }
    return referencedReachedSets;
  }

  private void writeArg(final Path file,
                        final Multimap<ARGState, ARGState> connections,
                        final Set<ARGState> rootStates) {
    try (Writer w = Files.openOutputFile(file)) {
      LazyARGToDotWriter.write(w,
              rootStates,
              connections,
              ARGUtils.CHILDREN_OF_STATE,
              Predicates.alwaysTrue(),
              highlightSummaryEdge);
    } catch (IOException e) {
      CPAMain.logManager.logUserException(Level.WARNING, e, String.format("Could not write ARG to file: %s", file));
    }
  }



  private final Predicate<Pair<ARGState,ARGState>> highlightSummaryEdge = new Predicate<Pair<ARGState, ARGState>>() {
    @Override
    public boolean apply(Pair<ARGState, ARGState> input) {
      final CFAEdge edge = input.getFirst().getEdgeToChild(input.getSecond());
      return edge instanceof FunctionSummaryEdge;
    }
  };
}
