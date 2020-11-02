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

import static com.google.common.base.Preconditions.checkState;
import static org.sosy_lab.cpachecker.util.statistics.StatisticsUtils.toPercent;

import java.io.IOException;
import java.io.PrintStream;
import java.io.Writer;
import java.text.DecimalFormat;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
import java.util.logging.Level;

import org.sosy_lab.common.Pair;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.Files;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.PathTemplate;
import org.sosy_lab.common.io.Paths;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.FunctionSummaryEdge;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGToDotWriter;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.bam.incremental.AbstractType;
import org.sosy_lab.cpachecker.cpa.bam.incremental.IncrementalCache;
import org.sosy_lab.cpachecker.cpa.bam.incremental.PredicateAnalysisEqualHelpState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.ProgramInfo;

import com.google.common.base.Predicate;
import com.google.common.base.Predicates;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedHelper;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;

/**
 * Prints some BAM related statistics
 */
@Options(prefix="cpa.bam")
public class BAMCPAStatistics implements Statistics {

  @Option(secure=true, description="export blocked ARG as .dot file")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  // private Path argFile = Paths.get("BlockedARG.dot");
  private Path argFile = null;

  @Option(secure=true, description="export single blocked ARG as .dot files, should contain '%d'")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  private PathTemplate indexedArgFile = PathTemplate.ofFormatString("ARGs/ARG_%d.dot");

  @Option(secure=true, description="export used parts of blocked ARG as .dot file")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  // private Path simplifiedArgFile = Paths.get("BlockedARGSimplified.dot");
  private Path simplifiedArgFile = null;

  private final Predicate<Pair<ARGState,ARGState>> highlightSummaryEdge = new Predicate<Pair<ARGState, ARGState>>() {
    @Override
    public boolean apply(Pair<ARGState, ARGState> input) {
      final CFAEdge edge = input.getFirst().getEdgeToChild(input.getSecond());
      return edge instanceof FunctionSummaryEdge;
    }
  };

  private final BAMCPA cpa;
  private final BAMCache cache;
  private AbstractBAMBasedRefiner refiner = null;
  private final LogManager logger;

  public BAMCPAStatistics(BAMCPA cpa, BAMCache cache, Configuration config, LogManager logger)
          throws InvalidConfigurationException {
    config.inject(this);

    this.cpa = cpa;
    this.cache = cache;
    this.logger = logger;
  }

  @Override
  public String getName() {
    return "BAMCPA";
  }

  public void addRefiner(AbstractBAMBasedRefiner pRefiner) {
    checkState(refiner == null);
    refiner = pRefiner;
  }

  @Override
  public void printStatistics(PrintStream out, Result result, ReachedSet reached) {

    BAMTransferRelation transferRelation = cpa.getTransferRelation();
    TimedReducer reducer = cpa.getReducer();

  //Add to reached set all states from BAM cache
    Collection<ReachedSet> cachedStates = cache.getAllCachedReachedStates();
    for (ReachedSet set : cachedStates) {
      for (AbstractState state : set.asCollection()) {
        /* Method 'add' add state not only in list of reached states, but also in waitlist,
         * so we should delete it.
         */
        reached.add(state, set.getPrecision(state));
        reached.removeOnlyFromWaitlist(state);
      }
    }

    if(CPAMain.summaryOutputPath != null) {
      //TODO implement serializeSummary for valueAnalysis
      if(CPAMain.isUesTextSummary  || refiner.getClass().toGenericString().contains("value")) {
        IncrementalCache.getInstance().saveSummaryToFile(CPAMain.summaryOutputPath, reached);
      } else {
        IncrementalCache.getInstance().serializeSummary(CPAMain.summaryOutputPath, reached);
      }
      ProgramInfo.getInstance().saveFunctionInfo(CPAMain.summaryOutputPath);
    }

    int sumCalls = cache.cacheMisses + cache.partialCacheHits + cache.fullCacheHits;

    int sumARTElemets = 0;
//    for (ReachedSet subreached : BAMARGUtils.gatherReachedSets(cpa, reached).values()) {
//      sumARTElemets += subreached.size();
//    }

    out.println("Total size of all ARGs:                                         " + sumARTElemets);
    out.println("Maximum block depth:                                            " + transferRelation.maxRecursiveDepth);
    out.println("Total number of recursive CPA calls:                            " + sumCalls);
    out.println("  Number of cache misses:                                       " + cache.cacheMisses + " (" + toPercent(cache.cacheMisses, sumCalls) + " of all calls)");
    out.println("  Number of partial cache hits:                                 " + cache.partialCacheHits + " (" + toPercent(cache.partialCacheHits, sumCalls) + " of all calls)");
    out.println("  Number of full cache hits:                                    " + cache.fullCacheHits + " (" + toPercent(cache.fullCacheHits, sumCalls) + " of all calls)");
    if(CPAMain.isReuseSummary) {
      out.println("  Number of last version caches:                                " + BAMCache.lastVersionCache);
      out.println("  Number of last version can reuse caches:                      " + IncrementalCache.getInstance().getLastVCanUseSummarySize());
      out.println("  Number of last version cache hits:                            " + cache.lastVersionCacheHits + " (" + (cache.fullCacheHits > 0 ? toPercent(cache.lastVersionCacheHits, cache.fullCacheHits) : "0%") + " of all hits)");
      out.println("Total Number of All Function:                                   " + ProgramInfo.getInstance().getNowFunctionInfo().size());
      out.println("  Number of unchanged Function size:                            " + ProgramInfo.getInstance().getUnchangedFunSize() + " (" + toPercent(ProgramInfo.getInstance().getUnchangedFunSize(), ProgramInfo.getInstance().getNowFunctionInfo().size()) + ")");
      //out.println("Mutation Rate:                                                  " + toPercent(ProgramInfo.getInstance().getChangedFunSet().size(), ProgramInfo.getInstance().getNowFunctionInfo().size()));
      out.println("Function summary hit rate:                                      " + toPercent(IncrementalCache.getInstance().funcHits, BAMCache.allTrys) + " (of " + BAMCache.allTrys + " trys)");
      out.println("Function cache hit rate:                                        " + toPercent(BAMCache.fullCacheHits, BAMCache.cacheMisses + BAMCache.partialCacheHits + BAMCache.fullCacheHits));
      out.println("Subgraph hits:                                                  " + BAMCache.subgraphHits);
      out.println("Summary file size:                            " +  GlobalInfo.getInstance().summary_fs);
      if(CPAMain.loopSummary){
        out.println("  Number of actual loop hits:                                 " + IncrementalCache.loopHits);
        out.println("  Number of loop summary:                                     " + IncrementalCache.getInstance().getLastVCanUseLoopSummarySize());
      }
    }
    if (cache.gatherCacheMissStatistics) {
      out.println("Cause for cache misses:                                         ");
      out.println("  Number of abstraction caused misses:                          " + cache.abstractionCausedMisses + " (" + toPercent(cache.abstractionCausedMisses, cache.cacheMisses) + " of all misses)");
      out.println("  Number of precision caused misses:                            " + cache.precisionCausedMisses + " (" + toPercent(cache.precisionCausedMisses, cache.cacheMisses) + " of all misses)");
      out.println("  Number of misses with no similar elements:                    " + cache.noSimilarCausedMisses + " (" + toPercent(cache.noSimilarCausedMisses, cache.cacheMisses) + " of all misses)");
    }
    if(CPAMain.isReuseSummary) {
      IncrementalCache incrementalCache = IncrementalCache.getInstance();
      ProgramInfo programInfo = ProgramInfo.getInstance();
      DecimalFormat format = new DecimalFormat("######0.000");
      double readPTime = Double.parseDouble(programInfo.getReadProgramInfoTimer().toString().replace("s", ""));
      double writePTime = Double.parseDouble(programInfo.getWriteProgramInfoTimer().toString().replace("s", ""));
      double diffPTime = Double.parseDouble(programInfo.getDifferProgramInfoTimer().toString().replace("s", ""));

      double isCacheHitTime = Double.parseDouble(incrementalCache.getIsCacheHitTimer().toString().replace("s", ""));
      double buildEqualHelpTime = 0;
      if(CPAMain.abstractType == AbstractType.PREDICATEANALYSIS) {
        buildEqualHelpTime = Double.parseDouble(PredicateAnalysisEqualHelpState.buildEqualHelpStateTimer.toString().replace("s", ""));
      }
      double readSummaryTime = Double.parseDouble(incrementalCache.getReadFileTimer().toString().replace("s", ""));
      double writeSummaryTime = Double.parseDouble(incrementalCache.getWriteFileTimer().toString().replace("s", ""));
      double totalAddedNotInATime = writeSummaryTime + readPTime + writePTime;
      double totalAddedInATime = isCacheHitTime + buildEqualHelpTime + readSummaryTime + diffPTime;
      out.println("Total added in analysis time:                                   " + format.format(totalAddedInATime) + "s");
      out.println("  Time for is cache hits:                                   " + incrementalCache.getIsCacheHitTimer() + " (Calls:" + incrementalCache.getIsCacheHitTimer().getNumberOfIntervals() + ")");
      if(CPAMain.abstractType == AbstractType.PREDICATEANALYSIS) {
        out.println("  Time for build equal help states:                         " + PredicateAnalysisEqualHelpState.buildEqualHelpStateTimer);
      }
      out.println("  Time for read summary:                                    " + incrementalCache.getReadFileTimer());
      out.println("  Time for diff program info:                               " + programInfo.getDifferProgramInfoTimer());
      out.println("Total added not in analysis time:                               " + format.format(totalAddedNotInATime) + "s");
      out.println("  Time for write summary:                                   " + incrementalCache.getWriteFileTimer());
      out.println("  Time for read program info:                               " + programInfo.getReadProgramInfoTimer());
      out.println("  Time for write program info:                              " + programInfo.getWriteProgramInfoTimer());
    }
    out.println("Time for reducing abstract states:                            " + reducer.reduceTime + " (Calls: " + reducer.reduceTime.getNumberOfIntervals() + ")");
    out.println("Time for expanding abstract states:                           " + reducer.expandTime + " (Calls: " + reducer.expandTime.getNumberOfIntervals() + ")");
    out.println("Time for checking equality of abstract states:                " + cache.equalsTimer + " (Calls: " + cache.equalsTimer.getNumberOfIntervals() + ")");
    out.println("Time for computing the hashCode of abstract states:           " + cache.hashingTimer + " (Calls: " + cache.hashingTimer.getNumberOfIntervals() + ")");
    out.println("Time for searching for similar cache entries:                   " + cache.searchingTimer + " (Calls: " + cache.searchingTimer.getNumberOfIntervals() + ")");
    out.println("Time for reducing precisions:                                   " + reducer.reducePrecisionTime + " (Calls: " + reducer.reducePrecisionTime.getNumberOfIntervals() + ")");
    out.println("Time for expanding precisions:                                  " + reducer.expandPrecisionTime + " (Calls: " + reducer.expandPrecisionTime.getNumberOfIntervals() + ")");

    out.println("Time for removing cached subtrees for refinement:               " + transferRelation.removeCachedSubtreeTimer);
    out.println("Time for recomputing ARGs during counterexample analysis:       " + transferRelation.recomputeARTTimer);
    if (refiner != null) {
      out.println("Compute path for refinement:                                    " + refiner.computePathTimer);
      out.println("  Constructing flat ARG:                                        " + refiner.computeSubtreeTimer);
      out.println("  Searching path to error location:                             " + refiner.computeCounterexampleTimer);
    }

    exportAllReachedSets(argFile, indexedArgFile, reached);
    exportUsedReachedSets(simplifiedArgFile, reached);
  }

  public void exportAllReachedSets(final Path superArgFile, final PathTemplate indexedFile,
                                      final UnmodifiableReachedSet mainReachedSet) {

    if (superArgFile != null) {

      final Set<UnmodifiableReachedSet> allReachedSets = new HashSet<>();
      allReachedSets.addAll(cache.getAllCachedReachedStates());
      allReachedSets.add(mainReachedSet);

      final Set<ARGState> rootStates = new HashSet<>();
      final Multimap<ARGState, ARGState> connections = HashMultimap.create();

      for (final UnmodifiableReachedSet reachedSet : allReachedSets) {
        ARGState rootState = (ARGState) reachedSet.getFirstState();
        rootStates.add(rootState);
        Multimap<ARGState, ARGState> localConnections = HashMultimap.create();
        getConnections(rootState, localConnections);
        connections.putAll(localConnections);

        // dump small graph
        writeArg(indexedFile.getPath(((ARGState) reachedSet.getFirstState()).getStateId()),
                localConnections, Collections.singleton((ARGState) reachedSet.getFirstState()));
      }

      // dump super-graph
      writeArg(superArgFile, connections, rootStates);
    }
  }

  /** dump only those ReachedSets, that are reachable from mainReachedSet. */
  private void exportUsedReachedSets(final Path superArgFile, final UnmodifiableReachedSet mainReachedSet) {

    if (superArgFile != null) {

      final Multimap<ARGState, ARGState> connections = HashMultimap.create();
      final Set<ARGState> rootStates = getUsedRootStates(mainReachedSet, connections);
      writeArg(superArgFile, connections, rootStates);
    }
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

  /**
   * This method iterates over all reachable states from rootState
   * and searches for connections to other reachedSets (a set of all those other reachedSets is returned).
   * As side-effect we collect a Multimap of all connections:
   * - from a state (in current reachedSet) to its reduced state (in other rechedSet) and
   * - from a foreign state (in other reachedSet) to its expanded state(s) (in current reachedSet).
   */
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
      if (cpa.getTransferRelation().abstractStateToReachedSet.containsKey(state)) {
        ReachedSet target = cpa.getTransferRelation().abstractStateToReachedSet.get(state);
        referencedReachedSets.add(target);
        ARGState targetState = (ARGState) target.getFirstState();
        connections.put(state, targetState);
      }
      if (cpa.getTransferRelation().expandedToReducedCache.containsKey(state)) {
        AbstractState sourceState = cpa.getTransferRelation().expandedToReducedCache.get(state);
        connections.put((ARGState) sourceState, state);
      }
      waitlist.addAll(state.getChildren());
    }
    return referencedReachedSets;
  }
}
