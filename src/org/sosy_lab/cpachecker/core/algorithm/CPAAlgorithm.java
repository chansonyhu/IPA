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
package org.sosy_lab.cpachecker.core.algorithm;


import static org.sosy_lab.cpachecker.util.AbstractStates.extractStateByType;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;

import javax.annotation.Nullable;

import javax.management.JMException;
import org.mockito.internal.matchers.Null;
import org.sosy_lab.common.Classes;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.ClassOption;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.time.TimeSpan;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.defaults.MergeSepOperator;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AlgorithmIterationListener;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.ForcedCovering;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustmentResult;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustmentResult.Action;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGMergeJoinCPAEnabledAnalysis;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.RefineHelper;
import org.sosy_lab.cpachecker.cpa.composite.CompositePrecision;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedHelper;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedState;
import org.sosy_lab.cpachecker.cpa.impacted.IncrementalPAUtil;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.modifications.ModificationsCPA;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.UnsupportedCCodeException;
import org.sosy_lab.cpachecker.util.AbstractStates;

import com.google.common.base.Functions;
import com.google.common.base.Optional;
import com.google.common.collect.Iterables;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.resources.ProcessCpuTime;

public class CPAAlgorithm implements Algorithm, StatisticsProvider {


  public static long cputimeCPA = 0;
  public static long cputimeCPAInterval = -1;

  private static class CPAStatistics implements Statistics {

    private Timer totalTimer         = new Timer();
    private Timer chooseTimer        = new Timer();
    private Timer precisionTimer     = new Timer();
    private Timer transferTimer      = new Timer();
    private Timer mergeTimer         = new Timer();
    private Timer stopTimer          = new Timer();
    private Timer addTimer           = new Timer();
    private Timer forcedCoveringTimer = new Timer();

    private int   countIterations   = 0;
    private int   maxWaitlistSize   = 0;
    private long  countWaitlistSize = 0;
    private int   countSuccessors   = 0;
    private int   maxSuccessors     = 0;
    private int   countMerge        = 0;
    private int   countStop         = 0;
    private int   countBreak        = 0;


    @Override
    public String getName() {
      return "CPA algorithm";
    }

    @Override
    public void printStatistics(PrintStream out, Result pResult,
        ReachedSet pReached) {
      out.println("Number of iterations:            " + countIterations);
      if (countIterations == 0) {
        // Statistics not relevant, prevent division by zero
        return;
      }

      out.println("Max size of waitlist:            " + maxWaitlistSize);
      out.println("Average size of waitlist:        " + countWaitlistSize
          / countIterations);
      out.println("Number of computed successors:   " + countSuccessors);
      out.println("Max successors for one state:    " + maxSuccessors);
      out.println("Number of times merged:          " + countMerge);
      out.println("Number of times stopped:         " + countStop);
      out.println("Number of times abs stopped:     " + IncrementalPAUtil.getInstance().absStop);
      out.println("Number of times nonAbs stopped:  " + IncrementalPAUtil.getInstance().nonAbsStop);
      out.println("Number of coverage check (part): " + IncrementalPAUtil.getInstance().coverage_check);
      out.println("Number of times doAbstraction node:  " + ImpactedHelper.getInstance().doAbstractionNodeCount);
      out.println("Number of times breaked:         " + countBreak);
      out.println();
      out.println("Total time for CPA algorithm:     " + totalTimer + " (Max: " + totalTimer.getMaxTime().formatAs(TimeUnit.SECONDS) + ")");
      out.println("CPU time for CPA algorithm:       " + TimeSpan.ofNanos(cputimeCPA).formatAs(TimeUnit.SECONDS));
      out.println("  Time for choose from waitlist:  " + chooseTimer);
      if (forcedCoveringTimer.getNumberOfIntervals() > 0) {
        out.println("  Time for forced covering:       " + forcedCoveringTimer);
      }
      out.println("  Time for precision adjustment:  " + precisionTimer);
      out.println("  Time for transfer relation:     " + transferTimer);
      if (mergeTimer.getNumberOfIntervals() > 0) {
        out.println("  Time for merge operator:        " + mergeTimer);
      }
      out.println("  Time for stop operator:         " + stopTimer);
      out.println("  Time for adding to reached set: " + addTimer);
    }
  }

  @Options(prefix="cpa")
  public static class CPAAlgorithmFactory {

    @Option(secure=true, description="Which strategy to use for forced coverings (empty for none)",
            name="forcedCovering")
    @ClassOption(packagePrefix="org.sosy_lab.cpachecker")
    private Class<? extends ForcedCovering> forcedCoveringClass = null;

    @Option(secure=true, description="Do not report 'False' result, return UNKNOWN instead. "
        + " Useful for incomplete analysis with no counterexample checking.")
    private boolean reportFalseAsUnknown = false;

    private final ForcedCovering forcedCovering;

    private final ConfigurableProgramAnalysis cpa;
    private final LogManager logger;
    private final ShutdownNotifier shutdownNotifier;
    private final AlgorithmIterationListener iterationListener;

    public CPAAlgorithmFactory(ConfigurableProgramAnalysis cpa, LogManager logger,
        Configuration config, ShutdownNotifier pShutdownNotifier,
        @Nullable AlgorithmIterationListener pIterationListener) throws InvalidConfigurationException {

      config.inject(this);
      this.cpa = cpa;
      this.logger = logger;
      this.shutdownNotifier = pShutdownNotifier;
      this.iterationListener = pIterationListener;

      if (forcedCoveringClass != null) {
        forcedCovering = Classes.createInstance(ForcedCovering.class, forcedCoveringClass,
            new Class<?>[] {Configuration.class, LogManager.class, ConfigurableProgramAnalysis.class},
            new Object[]   {config,              logger,           cpa});
      } else {
        forcedCovering = null;
      }

    }

    public CPAAlgorithm newInstance() {
      return new CPAAlgorithm(cpa, logger, shutdownNotifier, forcedCovering, iterationListener, reportFalseAsUnknown);
    }
  }

  public static CPAAlgorithm create(ConfigurableProgramAnalysis cpa, LogManager logger,
      Configuration config, ShutdownNotifier pShutdownNotifier,
      AlgorithmIterationListener pIterationListener) throws InvalidConfigurationException {

    return new CPAAlgorithmFactory(cpa, logger, config, pShutdownNotifier, pIterationListener).newInstance();
  }

  public static CPAAlgorithm create(ConfigurableProgramAnalysis cpa, LogManager logger,
      Configuration config, ShutdownNotifier pShutdownNotifier) throws InvalidConfigurationException {

    return new CPAAlgorithmFactory(cpa, logger, config, pShutdownNotifier, null).newInstance();
  }


  private final ForcedCovering forcedCovering;

  private final CPAStatistics               stats = new CPAStatistics();

  private final ConfigurableProgramAnalysis cpa;

  private final LogManager                  logger;

  private final ShutdownNotifier                   shutdownNotifier;

  private final AlgorithmIterationListener  iterationListener;

  private final AlgorithmStatus status;

  private CPAAlgorithm(ConfigurableProgramAnalysis cpa, LogManager logger,
      ShutdownNotifier pShutdownNotifier,
      ForcedCovering pForcedCovering,
      AlgorithmIterationListener pIterationListener,
      boolean pIsImprecise) {

    this.cpa = cpa;
    this.logger = logger;
    this.shutdownNotifier = pShutdownNotifier;
    this.forcedCovering = pForcedCovering;
    this.iterationListener = pIterationListener;
    status = AlgorithmStatus.SOUND_AND_PRECISE.withPrecise(!pIsImprecise);
  }

  @Override
  public AlgorithmStatus run(final ReachedSet reachedSet) throws CPAException, InterruptedException {
    stats.totalTimer.start();
    long startCPA = -1;
    try {
      startCPA = ProcessCpuTime.read();
    } catch (JMException pE) {
      pE.printStackTrace();
    }
    try {
      if(CPAMain.isIncPred && IncrementalPAUtil.isInit) {
        return run2(reachedSet);
      } else {
        return run0(reachedSet);
      }
    } finally {
      long endCPA = -1;
      try {
        endCPA = ProcessCpuTime.read();
      } catch (JMException pE) {
        pE.printStackTrace();
      }
      cputimeCPAInterval = endCPA - startCPA;
      cputimeCPA += cputimeCPAInterval;
      stats.totalTimer.stopIfRunning();
      stats.chooseTimer.stopIfRunning();
      stats.precisionTimer.stopIfRunning();
      stats.transferTimer.stopIfRunning();
      stats.mergeTimer.stopIfRunning();
      stats.stopTimer.stopIfRunning();
      stats.addTimer.stopIfRunning();
      stats.forcedCoveringTimer.stopIfRunning();
    }
  }

  private AlgorithmStatus run0(final ReachedSet reachedSet) throws CPAException, InterruptedException {
    final TransferRelation transferRelation = cpa.getTransferRelation();
    final MergeOperator mergeOperator = cpa.getMergeOperator();
    final StopOperator stopOperator = cpa.getStopOperator();
    final PrecisionAdjustment precisionAdjustment =
        cpa.getPrecisionAdjustment();

    while (reachedSet.hasWaitingState()) {
      shutdownNotifier.shutdownIfNecessary();

      stats.countIterations++;

      // Pick next state using strategy
      // BFS, DFS or top sort according to the configuration
      int size = reachedSet.getWaitlist().size();
      if (size >= stats.maxWaitlistSize) {
        stats.maxWaitlistSize = size;
      }
      stats.countWaitlistSize += size;

      stats.chooseTimer.start();
      final AbstractState state = reachedSet.popFromWaitlist();
      final Precision precision = reachedSet.getPrecision(state);
      stats.chooseTimer.stop();

      logger.log(Level.FINER, "Retrieved state from waitlist");
      logger.log(Level.ALL, "Current state is", state, "with precision",
          precision);

      if (forcedCovering != null) {
        stats.forcedCoveringTimer.start();
        try {
          boolean stop = forcedCovering.tryForcedCovering(state, precision, reachedSet);

          if (stop) {
            // TODO: remove state from reached set?
            continue;
          }
        } finally {
          stats.forcedCoveringTimer.stop();
        }
      }

      stats.transferTimer.start();
      Collection<? extends AbstractState> successors;
      try {
        ImpactedHelper.isHit = false;
        GlobalInfo.getInstance().currentReached = reachedSet;
        successors = transferRelation.getAbstractSuccessors(state, precision);
      } finally {
        stats.transferTimer.stop();
      }
      if(state instanceof ARGState && !ImpactedHelper.getInstance().isCheckingCEX) {
        if(GlobalInfo.ImpactedCPAPos != -1) {
          AbstractState iS =
              ((CompositeState) ((ARGState) state).getWrappedState()).getWrappedStates()
                  .get(GlobalInfo.ImpactedCPAPos);
          if (iS instanceof ImpactedState) {
            int curImpactedNum = ((ImpactedState) iS).getImpactedVariables().size();
            if (curImpactedNum > ImpactedHelper.getInstance().maxImpactedNumWhenCPA) {
              ImpactedHelper.getInstance().maxImpactedNumWhenCPA = curImpactedNum;
            }
          }
        }
      }

      // TODO When we have a nice way to mark the analysis result as incomplete,
      // we could continue analysis on a CPATransferException with the next state from waitlist.

      int numSuccessors = successors.size();
      logger.log(Level.FINER, "Current state has", numSuccessors,
          "successors");
      stats.countSuccessors += numSuccessors;
      stats.maxSuccessors = Math.max(numSuccessors, stats.maxSuccessors);
      if(RefineHelper.rerunning && AbstractStates.extractLocation(state).getNodeNumber() == RefineHelper.rerun_Leavenode
              && numSuccessors == 0) {
        //while(reachedSet.hasWaitingState())
        //  reachedSet.popFromWaitlist();
        RefineHelper.breakFromSuccessorAnalysis = true;
        break;
      }
      for (AbstractState successor : Iterables.consumingIterable(successors)) {
        logger.log(Level.FINER, "Considering successor of current state");
        logger.log(Level.ALL, "Successor of", state, "\nis", successor);

          stats.precisionTimer.start();
          PrecisionAdjustmentResult precAdjustmentResult;
          try {
            Optional<PrecisionAdjustmentResult> precAdjustmentOptional =
                    precisionAdjustment.prec(
                            successor, precision, reachedSet,
                            Functions.<AbstractState>identity(),
                            successor);
            if (!precAdjustmentOptional.isPresent()) {
              continue;
            }
            precAdjustmentResult = precAdjustmentOptional.get();
          } finally {
            stats.precisionTimer.stop();
          }


          successor = precAdjustmentResult.abstractState();
          Precision successorPrecision = precAdjustmentResult.precision();
          Action action = precAdjustmentResult.action();
          if(successor instanceof ARGState) {
            ((ARGState) successor).action = action;
          }
        //} else {

        //}

//        precisionAdjustment class:BAMPrecisionAdjustment

        if (action == Action.BREAK) {
          stats.stopTimer.start();
          boolean stop;
          try {
            stop = stopOperator.stop(successor, reachedSet.getReached(successor), successorPrecision);
          } finally {
            stats.stopTimer.stop();
          }

          if (AbstractStates.isTargetState(successor) && stop) {
            // don't signal BREAK for covered states
            // no need to call merge and stop either, so just ignore this state
            // and handle next successor
            stats.countStop++;
            logger.log(Level.FINER,
                "Break was signalled but ignored because the state is covered.");
            continue;

          } else {
            stats.countBreak++;
            logger.log(Level.FINER, "Break signalled, CPAAlgorithm will stop.");

            // add the new state
            reachedSet.add(successor, successorPrecision);

            if (!successors.isEmpty()) {
              // re-add the old state to the waitlist, there are unhandled
              // successors left that otherwise would be forgotten
              reachedSet.reAddToWaitlist(state);
            }
            return status;
          }
        }
        assert action == Action.CONTINUE : "Enum Action has unhandled values!";

        Collection<AbstractState> reached = reachedSet.getReached(successor);

        // reached = reachedSet.getReached(AbstractStates.extractLocation(successor));
        // An optimization, we don't bother merging if we know that the
        // merge operator won't do anything (i.e., it is merge-sep).
        if (mergeOperator != MergeSepOperator.getInstance() && !reached.isEmpty()) {
          stats.mergeTimer.start();
          try {
            List<AbstractState> toRemove = new ArrayList<>();
            List<Pair<AbstractState, Precision>> toAdd = new ArrayList<>();

            logger.log(Level.FINER, "Considering", reached.size(),
                "states from reached set for merge");
            for (AbstractState reachedState : reached) {
              if(!CPAMain.isIncPred && !ImpactedHelper.getInstance().readyForAnalysis) {
                ImpactedState imSuccessor = AbstractStates.extractStateByType(successor,
                    ImpactedState.class);
                ImpactedState imReachedState = AbstractStates.extractStateByType(reachedState,
                    ImpactedState.class);
                if(imSuccessor.getImpactedVariables().containsAll(imReachedState.getImpactedVariables()))
                  continue;
              }
              IncrementalPAUtil.getInstance().curTarget = -1;
              AbstractState mergedState =
                  mergeOperator.merge(successor, reachedState,
                      successorPrecision);

              PredicateAbstractState predSucc = extractStateByType(successor,
                  PredicateAbstractState.class);
              PredicateAbstractState predMerged = extractStateByType(mergedState,
                  PredicateAbstractState.class);
              assert predSucc != null;

              if (!mergedState.equals(reachedState)) {
                logger.log(Level.FINER,
                    "Successor was merged with state from reached set");
                logger.log(Level.ALL, "Merged", successor, "\nand",
                    reachedState, "\n-->", mergedState);
                stats.countMerge++;

                toRemove.add(reachedState);
                toAdd.add(Pair.of(mergedState, successorPrecision));
              }
            }
            reachedSet.removeAll(toRemove);
            reachedSet.addAll(toAdd);

            if (mergeOperator instanceof ARGMergeJoinCPAEnabledAnalysis) {
              ((ARGMergeJoinCPAEnabledAnalysis)mergeOperator).cleanUp(reachedSet);
            }

          } finally {
            stats.mergeTimer.stop();
          }
        }

        stats.stopTimer.start();
        boolean stop;
        try {
          stop = stopOperator.stop(successor, reached, successorPrecision);
          IncrementalPAUtil.getInstance().curTarget = -1;
        } finally {
          stats.stopTimer.stop();
        }

        if (stop) {
          logger.log(Level.FINER,
              "Successor is covered or unreachable, not adding to waitlist");
          stats.countStop++;
        } else {
          logger.log(Level.FINER,
              "No need to stop, adding successor to waitlist");

          stats.addTimer.start();
          reachedSet.add(successor, successorPrecision);
          stats.addTimer.stop();
        }
      }

      if (iterationListener != null) {
        iterationListener.afterAlgorithmIteration(this, reachedSet);
      }
    }
    return status;
  }

  private AlgorithmStatus run1(final ReachedSet reachedSet) throws CPAException, InterruptedException {
    final TransferRelation transferRelation = cpa.getTransferRelation();
    final MergeOperator mergeOperator = cpa.getMergeOperator();
    final StopOperator stopOperator = cpa.getStopOperator();
    final PrecisionAdjustment precisionAdjustment =
        cpa.getPrecisionAdjustment();

    while (reachedSet.hasWaitingState()) {
      shutdownNotifier.shutdownIfNecessary();

      stats.countIterations++;

      // Pick next state using strategy
      // BFS, DFS or top sort according to the configuration
      int size = reachedSet.getWaitlist().size();
      if (size >= stats.maxWaitlistSize) {
        stats.maxWaitlistSize = size;
      }
      stats.countWaitlistSize += size;

      stats.chooseTimer.start();
      final AbstractState state = reachedSet.popFromWaitlist();
      final Precision precision = reachedSet.getPrecision(state);
      stats.chooseTimer.stop();

      logger.log(Level.FINER, "Retrieved state from waitlist");
      logger.log(Level.ALL, "Current state is", state, "with precision",
          precision);

      if (forcedCovering != null) {
        stats.forcedCoveringTimer.start();
        try {
          boolean stop = forcedCovering.tryForcedCovering(state, precision, reachedSet);

          if (stop) {
            // TODO: remove state from reached set?
            continue;
          }
        } finally {
          stats.forcedCoveringTimer.stop();
        }
      }

      stats.transferTimer.start();
      Collection<? extends AbstractState> successors;
      try {
        ImpactedHelper.isHit = false;
        successors = transferRelation.getAbstractSuccessors(state, precision);
      } finally {
        stats.transferTimer.stop();
      }
      if(state instanceof ARGState) {
        if(GlobalInfo.ImpactedCPAPos != -1) {
          AbstractState iS =
              ((CompositeState) ((ARGState) state).getWrappedState()).getWrappedStates()
                  .get(GlobalInfo.ImpactedCPAPos);
          //assert iS instanceof ImpactedState;
          if (iS instanceof ImpactedState) {
            int curImpactedNum = ((ImpactedState) iS).getImpactedVariables().size();
            if (curImpactedNum > ImpactedHelper.getInstance().maxImpactedNumWhenCPA) {
              ImpactedHelper.getInstance().maxImpactedNumWhenCPA = curImpactedNum;
            }
          }
        }
      }

      // TODO When we have a nice way to mark the analysis result as incomplete,
      // we could continue analysis on a CPATransferException with the next state from waitlist.

      int numSuccessors = successors.size();
      logger.log(Level.FINER, "Current state has", numSuccessors,
          "successors");
      stats.countSuccessors += numSuccessors;
      stats.maxSuccessors = Math.max(numSuccessors, stats.maxSuccessors);
      if(RefineHelper.rerunning && AbstractStates.extractLocation(state).getNodeNumber() == RefineHelper.rerun_Leavenode
          && numSuccessors == 0) {
        //while(reachedSet.hasWaitingState())
        //  reachedSet.popFromWaitlist();
        RefineHelper.breakFromSuccessorAnalysis = true;
        break;
      }
      for (AbstractState successor : Iterables.consumingIterable(successors)) {
        int target = ((ARGState) state).target;
        int succLoc = AbstractStates.extractLocation(successor).getNodeNumber();
        if(target != succLoc && target != -1)
          continue;
        logger.log(Level.FINER, "Considering successor of current state");
        logger.log(Level.ALL, "Successor of", state, "\nis", successor);

        //if(!CPAMain.isReuseInvariant) {
        stats.precisionTimer.start();
        PrecisionAdjustmentResult precAdjustmentResult;
        try {
          Optional<PrecisionAdjustmentResult> precAdjustmentOptional =
              precisionAdjustment.prec(
                  successor, precision, reachedSet,
                  Functions.<AbstractState>identity(),
                  successor);
          if (!precAdjustmentOptional.isPresent()) {
            continue;
          }
          precAdjustmentResult = precAdjustmentOptional.get();
        } finally {
          stats.precisionTimer.stop();
        }
        PredicateAbstractState original = AbstractStates.extractStateByType(successor,
            PredicateAbstractState.class);
        PredicateAbstractState current = AbstractStates.extractStateByType(precAdjustmentResult.abstractState(),
            PredicateAbstractState.class);
//        boolean fixedAbs = false;
//        try {
//          if (original.getAbstractionFormula().equals(current.getAbstractionFormula())) {
//            // throw new UnsupportedOperationException("yqs17: TODO incremental PA ");
//            // System.out.println("yqs17: TODO incremental PA ");
//            // yqs17: 新计算得到的状态（current）和原来的状态（original）相等
//            fixedAbs = true;
//          }
//        } catch (NullPointerException npe) {
//          if(original == null) {
//            // System.out.println("original state is null");
//          } else if(current == null) {
//            // System.out.println("current state is null");
//          }
//        }
        successor = precAdjustmentResult.abstractState();
        Precision successorPrecision = precAdjustmentResult.precision();
        Action action = precAdjustmentResult.action();
        if(successor instanceof ARGState) {
          ((ARGState) successor).action = action;
        }
        //} else {

        //}

//        precisionAdjustment class:BAMPrecisionAdjustment

        if (action == Action.BREAK) {
          stats.stopTimer.start();
          boolean stop;
          try {
            stop = stopOperator.stop(successor, reachedSet.getReached(successor), successorPrecision);
          } finally {
            stats.stopTimer.stop();
          }

          if (AbstractStates.isTargetState(successor) && stop) {
            // don't signal BREAK for covered states
            // no need to call merge and stop either, so just ignore this state
            // and handle next successor
            stats.countStop++;
            logger.log(Level.FINER,
                "Break was signalled but ignored because the state is covered.");
            continue;

          } else {
            stats.countBreak++;
            logger.log(Level.FINER, "Break signalled, CPAAlgorithm will stop.");

            // add the new state
            reachedSet.add(successor, successorPrecision);

            if (!successors.isEmpty()) {
              // re-add the old state to the waitlist, there are unhandled
              // successors left that otherwise would be forgotten
              reachedSet.reAddToWaitlist(state);
            }
            // throw new UnsupportedOperationException("yqs17: incremental PA");
            return status;
          }
        }
        assert action == Action.CONTINUE : "Enum Action has unhandled values!";

        Collection<AbstractState> reached = reachedSet.getReached(successor);

        // An optimization, we don't bother merging if we know that the
        // merge operator won't do anything (i.e., it is merge-sep).
        if (mergeOperator != MergeSepOperator.getInstance() && !reached.isEmpty()) {
          stats.mergeTimer.start();
          try {
            List<AbstractState> toRemove = new ArrayList<>();
            List<Pair<AbstractState, Precision>> toAdd = new ArrayList<>();

            logger.log(Level.FINER, "Considering", reached.size(),
                "states from reached set for merge");
            for (AbstractState reachedState : reached) {
              AbstractState mergedState =
                  mergeOperator.merge(successor, reachedState,
                      successorPrecision);

              if (!mergedState.equals(reachedState)) {
                logger.log(Level.FINER,
                    "Successor was merged with state from reached set");
                logger.log(Level.ALL, "Merged", successor, "\nand",
                    reachedState, "\n-->", mergedState);
                stats.countMerge++;
                toRemove.add(reachedState);
                //if(!state.equals(mergedState))
                PredicateAbstractState currentMerge =
                    AbstractStates.extractStateByType(mergedState,
                    PredicateAbstractState.class);
                if(!original.getAbstractionFormula().equals(currentMerge.getAbstractionFormula())) {
                  toAdd.add(Pair.of(mergedState, successorPrecision));
                }
              }
            }
            // inc_pred: After merger, we judge whether the abs state is changed
//            if(!(toRemove.size() == 0 && toAdd.size() == 0))
//              System.out.println("yqs17: incremental PA: need to review");
            reachedSet.removeAll(toRemove);
            reachedSet.addAll(toAdd);

            if (mergeOperator instanceof ARGMergeJoinCPAEnabledAnalysis) {
              ((ARGMergeJoinCPAEnabledAnalysis)mergeOperator).cleanUp(reachedSet);
            }
            //throw new UnsupportedOperationException("yqs17: incremental PA");
          } finally {
            stats.mergeTimer.stop();
          }
        }

        stats.stopTimer.start();
        boolean stop;
        try {
          stop = stopOperator.stop(successor, reached, successorPrecision);
        } finally {
          stats.stopTimer.stop();
        }

        if (stop) {
          logger.log(Level.FINER,
              "Successor is covered or unreachable, not adding to waitlist");
          stats.countStop++;
        } else {
          logger.log(Level.FINER,
              "No need to stop, adding successor to waitlist");

          stats.addTimer.start();
          // yqs17: 只添加发生变化的状态的后继状态
          // if(!fixedAbs)
            reachedSet.add(successor, successorPrecision);
          stats.addTimer.stop();
        }
      }

      if (iterationListener != null) {
        iterationListener.afterAlgorithmIteration(this, reachedSet);
      }
    }

    return status;
  }

  private AlgorithmStatus run2(final ReachedSet reachedSet) throws CPAException,
                                                                   InterruptedException {
    final TransferRelation transferRelation = cpa.getTransferRelation();
    final MergeOperator mergeOperator = cpa.getMergeOperator();
    final StopOperator stopOperator = cpa.getStopOperator();
    final PrecisionAdjustment precisionAdjustment =
        cpa.getPrecisionAdjustment();

    while (reachedSet.hasWaitingState()) {
      shutdownNotifier.shutdownIfNecessary();

      stats.countIterations++;

      // Pick next state using strategy
      // BFS, DFS or top sort according to the configuration
      int size = reachedSet.getWaitlist().size();
      if (size >= stats.maxWaitlistSize) {
        stats.maxWaitlistSize = size;
      }
      stats.countWaitlistSize += size;

      stats.chooseTimer.start();
      final AbstractState state = reachedSet.popFromWaitlist();
      final Precision precision = reachedSet.getPrecision(state);
      stats.chooseTimer.stop();

      logger.log(Level.FINER, "Retrieved state from waitlist");
      logger.log(Level.ALL, "Current state is", state, "with precision",
          precision);

      if (forcedCovering != null) {
        stats.forcedCoveringTimer.start();
        try {
          boolean stop = forcedCovering.tryForcedCovering(state, precision, reachedSet);

          if (stop) {
            // TODO: remove state from reached set?
            continue;
          }
        } finally {
          stats.forcedCoveringTimer.stop();
        }
      }

      stats.transferTimer.start();
      Collection<? extends AbstractState> successors;
      try {
        ImpactedHelper.isHit = false;
        successors = transferRelation.getAbstractSuccessors(state, precision);
      } finally {
        stats.transferTimer.stop();
      }
      if(state instanceof ARGState) {
        if(GlobalInfo.ImpactedCPAPos != -1) {
          AbstractState iS =
              ((CompositeState) ((ARGState) state).getWrappedState()).getWrappedStates()
                  .get(GlobalInfo.ImpactedCPAPos);
          //assert iS instanceof ImpactedState;
          if (iS instanceof ImpactedState) {
            int curImpactedNum = ((ImpactedState) iS).getImpactedVariables().size();
            if (curImpactedNum > ImpactedHelper.getInstance().maxImpactedNumWhenCPA) {
              ImpactedHelper.getInstance().maxImpactedNumWhenCPA = curImpactedNum;
            }
          }
        }
      }

      // TODO When we have a nice way to mark the analysis result as incomplete,
      // we could continue analysis on a CPATransferException with the next state from waitlist.

      int numSuccessors = successors.size();
      logger.log(Level.FINER, "Current state has", numSuccessors,
          "successors");
      stats.countSuccessors += numSuccessors;
      stats.maxSuccessors = Math.max(numSuccessors, stats.maxSuccessors);

      for (AbstractState successor : Iterables.consumingIterable(successors)) {

        logger.log(Level.FINER, "Considering successor of current state");
        logger.log(Level.ALL, "Successor of", state, "\nis", successor);

        //if(!CPAMain.isReuseInvariant) {
        stats.precisionTimer.start();
        PrecisionAdjustmentResult precAdjustmentResult;
        try {
          Optional<PrecisionAdjustmentResult> precAdjustmentOptional =
              precisionAdjustment.prec(
                  successor, precision, reachedSet,
                  Functions.<AbstractState>identity(),
                  successor);
          if (!precAdjustmentOptional.isPresent()) {
            continue;
          }
          precAdjustmentResult = precAdjustmentOptional.get();
        } finally {
          stats.precisionTimer.stop();
        }

        successor = precAdjustmentResult.abstractState();
        Precision successorPrecision = precAdjustmentResult.precision();
        Action action = precAdjustmentResult.action();
        // yqs17: 因为在reached不sound前遇到target，会报出BREAK信号，这时候先暂时CONTINUE
        // yqs17: 去掉则从bottom断开，只重用前面部分的annotation
        if(CPAMain.isIncPred && action == Action.BREAK && reachedSet.hasWaitingState()) {
          //action = Action.CONTINUE;
        }
        if(successor instanceof ARGState) {
          ((ARGState) successor).action = action;
        }
        //} else {

        //}

//        precisionAdjustment class:BAMPrecisionAdjustment

        if (action == Action.BREAK) {
          stats.stopTimer.start();
          boolean stop;
          try {
            stop = stopOperator.stop(successor, reachedSet.getReached(successor), successorPrecision);
          } finally {
            stats.stopTimer.stop();
          }

          if (AbstractStates.isTargetState(successor) && stop) {
            // don't signal BREAK for covered states
            // no need to call merge and stop either, so just ignore this state
            // and handle next successor
            stats.countStop++;
            logger.log(Level.FINER,
                "Break was signalled but ignored because the state is covered.");
            continue;

          } else {
            stats.countBreak++;
            logger.log(Level.FINER, "Break signalled, CPAAlgorithm will stop.");

            // add the new state
            reachedSet.add(successor, successorPrecision);

            if (!successors.isEmpty()) {
              // re-add the old state to the waitlist, there are unhandled
              // successors left that otherwise would be forgotten
              reachedSet.reAddToWaitlist(state);
            }
            // throw new UnsupportedOperationException("yqs17: incremental PA");
            return status;
          }
        }
        assert action == Action.CONTINUE : "Enum Action has unhandled values!";

        Collection<AbstractState> reached = reachedSet.getReached(successor);

        // An optimization, we don't bother merging if we know that the
        // merge operator won't do anything (i.e., it is merge-sep).
        if (mergeOperator != MergeSepOperator.getInstance() && !reached.isEmpty()) {
          stats.mergeTimer.start();
          try {
            List<AbstractState> toRemove = new ArrayList<>();
            List<Pair<AbstractState, Precision>> toAdd = new ArrayList<>();

            logger.log(Level.FINER, "Considering", reached.size(),
                "states from reached set for merge");
            for (AbstractState reachedState : reached) {
              AbstractState mergedState =
                  mergeOperator.merge(successor, reachedState,
                      successorPrecision);

              if (!mergedState.equals(reachedState)) {
                logger.log(Level.FINER,
                    "Successor was merged with state from reached set");
                logger.log(Level.ALL, "Merged", successor, "\nand",
                    reachedState, "\n-->", mergedState);
                stats.countMerge++;
                toRemove.add(reachedState);
                //if(!state.equals(mergedState))
                PredicateAbstractState currentMerge =
                    AbstractStates.extractStateByType(mergedState,
                        PredicateAbstractState.class);
              }
            }
            reachedSet.removeAll(toRemove);
            reachedSet.addAll(toAdd);

            if (mergeOperator instanceof ARGMergeJoinCPAEnabledAnalysis) {
              ((ARGMergeJoinCPAEnabledAnalysis)mergeOperator).cleanUp(reachedSet);
            }
            //throw new UnsupportedOperationException("yqs17: incremental PA");
          } finally {
            stats.mergeTimer.stop();
          }
        }

        stats.stopTimer.start();
        boolean stop;
        try {
          stop = stopOperator.stop(successor, reached, successorPrecision);
//          stop = stopOperator.stop(successor,
//              reachedSet.getReached(AbstractStates.extractLocation(successor)),
//              successorPrecision);
        } finally {
          stats.stopTimer.stop();
        }

        if (stop) {
          logger.log(Level.FINER,
              "Successor is covered or unreachable, not adding to waitlist");
          stats.countStop++;
        } else {
          logger.log(Level.FINER,
              "No need to stop, adding successor to waitlist");

          stats.addTimer.start();
          reachedSet.add(successor, successorPrecision);
          stats.addTimer.stop();
        }
      }

      if (iterationListener != null) {
        iterationListener.afterAlgorithmIteration(this, reachedSet);
      }
    }

    return status;
  }

  @Override
  public void collectStatistics(Collection<Statistics> pStatsCollection) {
    if (forcedCovering instanceof StatisticsProvider) {
      ((StatisticsProvider)forcedCovering).collectStatistics(pStatsCollection);
    }
    pStatsCollection.add(stats);
  }
}
