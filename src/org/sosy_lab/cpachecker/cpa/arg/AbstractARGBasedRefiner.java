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
package org.sosy_lab.cpachecker.cpa.arg;

import static com.google.common.collect.FluentIterable.from;
import static org.sosy_lab.cpachecker.util.AbstractStates.IS_TARGET_STATE;

import java.io.IOException;
import java.io.Writer;
import java.util.*;
import java.util.logging.Level;

import javax.annotation.Nullable;

import com.google.common.base.Predicate;
import com.google.common.base.Predicates;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.io.Files;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.PathTemplate;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.blocks.Block;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionSummaryEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionCallEdge;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.CounterexampleInfo;
import org.sosy_lab.cpachecker.core.counterexample.RichModel;
import org.sosy_lab.cpachecker.core.interfaces.*;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.bam.BAMARGBlockStartState;
import org.sosy_lab.cpachecker.cpa.bam.BAMCPAStatistics;
import org.sosy_lab.cpachecker.cpa.bam.incremental.RefineHelper;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateCPARefiner;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.exceptions.RefinementFailedException;

import com.google.common.base.Function;
import com.google.common.base.Joiner;
import com.google.common.collect.Collections2;
import com.google.errorprone.annotations.ForOverride;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;

public abstract class AbstractARGBasedRefiner implements Refiner {

  private int refinementNumber;

  private final ARGCPA argCpa;
  private final LogManager logger;

  private int counterexamplesCounter = 0;


  protected AbstractARGBasedRefiner(ConfigurableProgramAnalysis pCpa) throws InvalidConfigurationException {
    if (pCpa instanceof WrapperCPA) {
      argCpa = ((WrapperCPA) pCpa).retrieveWrappedCpa(ARGCPA.class);
    } else {
      throw new InvalidConfigurationException("ARG CPA needed for refinement");
    }
    if (argCpa == null) {
      throw new InvalidConfigurationException("ARG CPA needed for refinement");
    }
    this.logger = argCpa.getLogger();
  }

  private static final Function<CFAEdge, String> pathToFunctionCalls
        = new Function<CFAEdge, String>() {
    @Override
    public String apply(CFAEdge arg) {

      if (arg instanceof CFunctionCallEdge) {
        CFunctionCallEdge funcEdge = (CFunctionCallEdge)arg;
        return funcEdge.toString();
      } else {
        return null;
      }
    }
  };

  @Override
  public final boolean performRefinement(ReachedSet pReached) throws CPAException, InterruptedException {
    logger.log(Level.FINEST, "Starting ARG based refinement");

    assert ARGUtils.checkARG(pReached) : "ARG and reached set do not match before refinement";

    ARGState lastElement = (ARGState)pReached.getLastState();
    //ARGState lastElement = (ARGState) from(pReached).filter(IS_TARGET_STATE).toList().get(0);
    if(!lastElement.isTarget()) {
      // lastElement = (ARGState) from(pReached).filter(IS_TARGET_STATE).toList().get(0);
      // yqs17: update 不重用target state，则lastElement一定为target
      throw new UnsupportedOperationException("yqs17: last state is not a target state");
    }
    assert lastElement.isTarget() : "Last element in reached is not a target state before refinement";
    ARGReachedSet reached = new ARGReachedSet(pReached, argCpa, refinementNumber++);

    ARGPath path = computePath(lastElement, reached);

    if(!(path == null)) {
      int path_key = path.hashCode();
      if (!RefineHelper.pathCounter.containsKey(path_key))
        RefineHelper.pathCounter.put(path_key, 0);
      else {
        Integer tmp = RefineHelper.pathCounter.get(path_key);
        tmp = tmp + 1;
        RefineHelper.pathCounter.put(path_key, tmp);
        if (tmp >= 20) {
          //RefineHelper.isExpanding = false;
          RefineHelper.samePath = true;
        }
      }
    }


    int curPathLength = (path == null ? 0 : path.getStateSet().size());

    logger.log(Level.INFO, "Path Length: " + (path == null ? 0 : path.getStateSet().size()));

    // System.out.println("Path Length: " + (path == null ? 0 : path.getStateSet().size()));

    if(curPathLength == GlobalInfo.getInstance().lastPathLength && curPathLength != 0) {
      GlobalInfo.getInstance().spltimes++;
      // System.out.println("SPL: " + GlobalInfo.getInstance().spltimes);
    } else {
      GlobalInfo.getInstance().spltimes = 0;
    }

    GlobalInfo.getInstance().lastPathLength = curPathLength;

    if (logger.wouldBeLogged(Level.ALL) && path != null) {
      logger.log(Level.ALL, "Error path:\n", path);
      logger.log(Level.ALL, "Function calls on Error path:\n",
          Joiner.on("\n ").skipNulls().join(Collections2.transform(path.getInnerEdges(), pathToFunctionCalls)));
    }

    CounterexampleInfo counterexample;
    //TODO only for debug
    if(RefineHelper.getInstance().isfullPath()) {
    //if(true){
      try {
        counterexample = performRefinement(reached, path);
        //System.out.println("dummy");
      } catch (RefinementFailedException e) {
        if (e.getErrorPath() == null) {
          e.setErrorPath(path);
        }

        // set the path from the exception as the target path
        // so it can be used for debugging
        argCpa.addCounterexample(lastElement, CounterexampleInfo.feasible(e.getErrorPath(), RichModel
                .empty()));
        throw e;
      }
    } else {

      //changed by cailiming
      counterexample = performRefinement(reached, path);
      if(counterexample.isSpurious() && !RefineHelper.getInstance().isfullPath() && !RefineHelper.samePrecision) {
        CPAMain.lazySucc = true;
        RefineHelper.holes.clear();
        RefineHelper.holes_content.clear();
      }
      while(!counterexample.isSpurious() && !RefineHelper.getInstance().isfullPath() || RefineHelper.samePrecision) {
      //while(true) {
        //RefineHelper.getInstance().setRetFromMiddle(false);
        //RefineHelper.getInstance().setRecover(true);
        RefineHelper.isExpanding = true;
        ARGPath npath = expandPath(path, RefineHelper.getInstance().getHole());
        RefineHelper.expansions++;
        if(npath != null) {
          logger.log(Level.INFO, "The expanded path is equal to the previous path: " + npath.equals(path));
          if (npath.equals(path)) {
            //counterexample = performRefinement(reached, path);
            RefineHelper.isExpanding = false;
            RefineHelper.samePath = true;
            break;
          }
        }
        //stats = new BAMCPAStatistics(this, cache, config, logger);

        path = npath;
        RefineHelper.samePath = false;
        counterexample = performRefinement(reached, path);
        if(RefineHelper.samePrecision) {
          RefineHelper.holes.clear();
          RefineHelper.holes_content.clear();
          RefineHelper.samePrecision = false;
        }

      }
      RefineHelper.isExpanding = false;
      if(!RefineHelper.getInstance().isfullPath()) {
        CPAMain.lazySucc = true;
      }
      RefineHelper.lazyBFCache.clear();
      //} while(!RefineHelper.getInstance().isfullPath());
      //counterexample = performRefinement(reached, path);
    }
    if(path != null)
      RefineHelper.pathLens += path.size();

    assert ARGUtils.checkARG(pReached) : "ARG and reached set do not match after refinement";

    //TODO for debug
    //counterexample = performRefinement(reached, path);

    if (!counterexample.isSpurious()) {
      ARGPath targetPath = counterexample.getTargetPath();

      // new targetPath must contain root and error node
      if (path != null) {
        assert targetPath.getFirstState() == path.getFirstState() : "Target path from refiner does not contain root node";
        assert targetPath.getLastState()  == path.getLastState() : "Target path from refiner does not contain target state";
      }

      argCpa.addCounterexample(lastElement, counterexample);

      logger.log(Level.FINEST, "Counterexample", counterexamplesCounter, "has been found.");

      // Print error trace if cpa.arg.printErrorPath = true
      argCpa.exportCounterexampleOnTheFly(lastElement, counterexample, counterexamplesCounter);
      counterexamplesCounter++;
    }

    logger.log(Level.FINEST, "ARG based refinement finished, result is", counterexample.isSpurious());

    return counterexample.isSpurious();
  }


  /**
   * Perform refinement.
   * @param pReached
   * @param pPath
   * @return Information about the counterexample.
   * @throws InterruptedException
   */
  protected abstract CounterexampleInfo performRefinement(ARGReachedSet pReached, ARGPath pPath)
            throws CPAException, InterruptedException;

  /**
   * This method may be overwritten if the standard behavior of <code>ARGUtils.getOnePathTo()</code> is not
   * appropriate in the implementations context.
   *
   * TODO: Currently this function may return null.
   *
   * @param pLastElement Last ARGState of the given reached set
   * @param pReached ReachedSet
   * @see org.sosy_lab.cpachecker.cpa.arg.ARGUtils
   * @return
   * @throws InterruptedException
   */
  @ForOverride
  @Nullable
  protected ARGPath computePath(ARGState pLastElement, ARGReachedSet pReached) throws InterruptedException, CPAException {
    return ARGUtils.getOnePathTo(pLastElement);
  }

  @ForOverride
  @Nullable
  protected ARGPath expandPath(ARGPath pPath, Pair<ARGState,Vector<Triple<Triple<AbstractState,Precision,Block>,ARGReachedSet,ARGState>>> holeSig) throws InterruptedException, CPATransferException {
    return null;
  }


  /*
  private void exportUsedReachedSets(final Path superArgFile, final UnmodifiableReachedSet mainReachedSet) {

    if (superArgFile != null) {

      final Multimap<ARGState, ARGState> connections = HashMultimap.create();
      final Set<ARGState> rootStates = getUsedRootStates(mainReachedSet, connections);
      writeArg(superArgFile, connections, rootStates);
    }
  }



  private Set<ARGState> getUsedRootStates(final UnmodifiableReachedSet mainReachedSet,
                                          final Multimap<ARGState, ARGState> connections) {
    final Set<UnmodifiableReachedSet> finished = new HashSet<>();
    final Deque<UnmodifiableReachedSet> waitlist = new ArrayDeque<>();
    waitlist.add(mainReachedSet);
    while (!waitlist.isEmpty()){
      final UnmodifiableReachedSet reachedSet = waitlist.pop();
      if (!finished.add(reachedSet)) {
        continue;
      }
      final ARGState rootState = (ARGState) reachedSet.getFirstState();
      final Set<ReachedSet> referencedReachedSets = getConnections(rootState, connections);
      waitlist.addAll(referencedReachedSets);
    }

    final Set<ARGState> rootStates = new HashSet<>();
    for (UnmodifiableReachedSet reachedSet : finished) {
      rootStates.add((ARGState)reachedSet.getFirstState());
    }
    return rootStates;
  }

  private Set<ReachedSet> getConnections(final ARGState rootState, final Multimap<ARGState, ARGState> connections) {
    final Set<ReachedSet> referencedReachedSets = new HashSet<>();
    final Set<ARGState> finished = new HashSet<>();
    final Deque<ARGState> waitlist = new ArrayDeque<>();
    waitlist.add(rootState);
    while (!waitlist.isEmpty()) {
      ARGState state = waitlist.pop();
      if (!finished.add(state)) {
        continue;
      }
      if (argCpa.getTransferRelation().abstractStateToReachedSet.containsKey(state)) {
        ReachedSet target = argCpa.getTransferRelation().abstractStateToReachedSet.get(state);
        referencedReachedSets.add(target);
        ARGState targetState = (ARGState) target.getFirstState();
        connections.put(state, targetState);
      }
      if (argCpa.getTransferRelation().expandedToReducedCache.containsKey(state)) {
        AbstractState sourceState = argCpa.getTransferRelation().expandedToReducedCache.get(state);
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
      ARGToDotWriter.write(w,
              rootStates,
              connections,
              ARGUtils.CHILDREN_OF_STATE,
              Predicates.alwaysTrue(),
              highlightSummaryEdge);
    } catch (IOException e) {
      logger.logUserException(Level.WARNING, e, String.format("Could not write ARG to file: %s", file));
    }
  }



  private final Predicate<Pair<ARGState,ARGState>> highlightSummaryEdge = new Predicate<Pair<ARGState, ARGState>>() {
    @Override
    public boolean apply(Pair<ARGState, ARGState> input) {
      final CFAEdge edge = input.getFirst().getEdgeToChild(input.getSecond());
      return edge instanceof FunctionSummaryEdge;
    }
  };
  */
}
