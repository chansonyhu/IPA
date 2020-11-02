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
package org.sosy_lab.cpachecker.core;

import static com.google.common.collect.FluentIterable.from;
import static org.sosy_lab.common.ShutdownNotifier.interruptCurrentThreadOnShutdown;
import static org.sosy_lab.cpachecker.util.AbstractStates.IS_TARGET_STATE;
import static org.sosy_lab.cpachecker.util.AbstractStates.extractLocation;

import com.google.common.base.Functions;
import com.google.common.base.Optional;
import com.google.common.base.Predicates;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Multimap;
import java.io.*;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;

import javax.annotation.Nullable;

import javax.management.JMException;
import org.sosy_lab.common.AbstractMBean;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.ShutdownNotifier.ShutdownRequestListener;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.FileOption.Type;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.Files;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.Paths;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.CFACreator;
import org.sosy_lab.cpachecker.cfa.Language;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.CoreComponentsFactory.SpecAutomatonCompositionType;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm;
import org.sosy_lab.cpachecker.core.algorithm.Algorithm.AlgorithmStatus;
import org.sosy_lab.cpachecker.core.algorithm.ExternalCBMCAlgorithm;
import org.sosy_lab.cpachecker.core.algorithm.impact.ImpactAlgorithm;
import org.sosy_lab.cpachecker.core.defaults.MergeSepOperator;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.interfaces.MergeOperator;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustmentResult;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustmentResult.Action;
import org.sosy_lab.cpachecker.core.interfaces.StateSpacePartition;
import org.sosy_lab.cpachecker.core.interfaces.StopOperator;
import org.sosy_lab.cpachecker.core.interfaces.Targetable;
import org.sosy_lab.cpachecker.core.interfaces.TransferRelation;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGMergeJoinCPAEnabledAnalysis;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.arg.ARGToDotWriter;
import org.sosy_lab.cpachecker.cpa.arg.ARGUtils;
import org.sosy_lab.cpachecker.cpa.bam.incremental.RefineHelper;
import org.sosy_lab.cpachecker.cpa.composite.CompositePrecision;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedCFAUtils;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedDiffer;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedHelper;
import org.sosy_lab.cpachecker.cpa.impacted.IncrementalPAUtil;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractionRefinementStrategy.PredicateSharing;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.ParserException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.LoopStructure;
import org.sosy_lab.cpachecker.util.LoopStructure.Loop;
import org.sosy_lab.cpachecker.util.Precisions;
import org.sosy_lab.cpachecker.util.UniqueIdGenerator;
import org.sosy_lab.cpachecker.util.automaton.TargetLocationProvider;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;

import com.google.common.base.Function;
import com.google.common.base.Joiner;
import com.google.common.base.Splitter;
import com.google.common.base.StandardSystemProperty;
import com.google.common.base.Strings;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSet.Builder;
import com.google.common.collect.Sets;
import com.google.common.io.Resources;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.resources.ProcessCpuTime;

@Options(prefix="analysis")
public class CPAchecker {
    @Option(
        secure = true,
        description = "Program to check against",
        name = "prev.program",
        required = true)
    @FileOption(Type.OPTIONAL_INPUT_FILE)
    private Path originalProgram = null;

    @Option(secure=true, name="initialARG.file",
        description="export initial ARG as .dot file")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    private Path argFile = Paths.get("InitialARG.dot");

    @Option(secure=true, name="initialSimplifiedARG.file",
        description="export final ARG as .dot file, showing only loop heads and function entries/exits")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    private Path simplifiedArgFile = Paths.get("InitialARGSimplified.dot");

    public static long cputimeInit = 0;
    public static long cputimePrec = 0;
    public static long impactedCpuTime = 0;
    public static long normalanalysisCpuTime = 0;
    public static long cfadiffCpuTime = 0;

    public static interface CPAcheckerMXBean {
        public int getReachedSetSize();

        public void stop();
    }

    private static class CPAcheckerBean extends AbstractMBean implements CPAcheckerMXBean {

        private final ReachedSet reached;
        private final ShutdownNotifier shutdownNotifier;

        public CPAcheckerBean(ReachedSet pReached, LogManager logger, ShutdownNotifier pShutdownNotifier) {
            super("org.sosy_lab.cpachecker:type=CPAchecker", logger);
            reached = pReached;
            shutdownNotifier = pShutdownNotifier;
            register();
        }

        @Override
        public int getReachedSetSize() {
            return reached.size();
        }

        @Override
        public void stop() {
            shutdownNotifier.requestShutdown("A stop request was received via the JMX interface.");
        }

    }

    @Option(secure=true, description="stop after the first error has been found")
    private boolean stopAfterError = true;

    @Option(secure=true, name="disable",
            description="stop CPAchecker after startup (internal option, not intended for users)")
    private boolean disableAnalysis = false;

    public static enum InitialStatesFor {
        /**
         * Function entry node of the entry function
         */
        ENTRY,

        /**
         * Set of function entry nodes of all functions.
         */
        FUNCTION_ENTRIES,

        /**
         * All locations that are possible targets of the analysis.
         */
        TARGET,

        /**
         * Function exit node of the entry function.
         */
        EXIT,

        /**
         * All function exit nodes of all functions and all loop heads of endless loops.
         */
        FUNCTION_SINKS,

        /**
         * All function exit nodes of the entry function, and all loop heads of endless loops.
         */
        PROGRAM_SINKS
    }

    @Option(secure=true, name="initialStatesFor",
            description="What CFA nodes should be the starting point of the analysis?")
    private Set<InitialStatesFor> initialStatesFor = Sets.newHashSet(InitialStatesFor.ENTRY);

    @Option(secure=true,
            description="Partition the initial states based on the type of location they were created for (see 'initialStatesFor')")
    private boolean partitionInitialStates = false;

    @Option(secure=true, name="algorithm.CBMC",
            description="use CBMC as an external tool from CPAchecker")
    private boolean runCBMCasExternalTool = false;

    @Option(secure=true, description="Do not report unknown if analysis terminated, report true (UNSOUND!).")
    private boolean unknownAsTrue = false;

    private final LogManager logger;
    public final Configuration config;
    private final ShutdownNotifier shutdownNotifier;
    private final CoreComponentsFactory factory;

    // The content of this String is read from a file that is created by the
    // ant task "init".
    // To change the version, update the property in build.xml.
    private static final String version;
    static {
        String v = "(unknown version)";
        try {
            URL url = CPAchecker.class.getClassLoader().getResource("org/sosy_lab/cpachecker/VERSION.txt");
            if (url != null) {
                String content = Resources.toString(url, StandardCharsets.US_ASCII).trim();
                if (content.matches("[a-zA-Z0-9 ._+:-]+")) {
                    v = content;
                }
            }
        } catch (IOException e) {
            // Ignore exception, no better idea what to do here.
        }
        version = v;
    }

    public static String getVersion() {
        return getCPAcheckerVersion()
                + " (" + StandardSystemProperty.JAVA_VM_NAME.value()
                +  " " + StandardSystemProperty.JAVA_VERSION.value() + ")";
    }

    public static String getCPAcheckerVersion() {
        return version;
    }

    public CPAchecker(Configuration pConfiguration, LogManager pLogManager,
                      ShutdownNotifier pShutdownNotifier) throws InvalidConfigurationException {
        config = pConfiguration;
        logger = pLogManager;
        shutdownNotifier = pShutdownNotifier;
//        if(config.getProperty("analysis.prev.program") == null){
//
//        }
        try {
            config.inject(this);
        } catch (Exception e) {

        }
        factory = new CoreComponentsFactory(pConfiguration, pLogManager, shutdownNotifier);
    }

    public CPAcheckerResult run(String programDenotation) {

        logger.log(Level.INFO, "CPAchecker", getVersion(), "started");

        MainCPAStatistics stats = null;
        ReachedSet reached = null;
        Result result = Result.NOT_YET_STARTED;
        String violatedPropertyDescription = "";

        final ShutdownRequestListener interruptThreadOnShutdown = interruptCurrentThreadOnShutdown();
        shutdownNotifier.register(interruptThreadOnShutdown);

        try {
            stats = new MainCPAStatistics(config, logger);

            // create reached set, cpa, algorithm
            stats.creationTime.start();
            reached = factory.createReachedSet();
            ImpactedHelper.getInstance().factory = factory;

            Algorithm algorithm;

            if (runCBMCasExternalTool) {

                checkIfOneValidFile(programDenotation);
                algorithm = new ExternalCBMCAlgorithm(programDenotation, config, logger);

            } else {
                CFA cfa = parse(programDenotation, stats);
                for(String functionName : cfa.getAllFunctionNames()) {
                    if(functionName.equals("ldv_error")) continue;
                    ImpactedHelper.getInstance().allFunctionNames.put(functionName,
                        cfa.getFunctionHead(functionName));
                }
                final SpecAutomatonCompositionType speComposition =
                    initialStatesFor.contains(InitialStatesFor.TARGET)
                    ? SpecAutomatonCompositionType.BACKWARD_TO_ENTRY_SPEC
                    : SpecAutomatonCompositionType.TARGET_SPEC;

                if(!ImpactedHelper.getInstance().externalDiff && CPAMain.isIncPred) {
                    stats.cfadiffTime.start();
                    CFANode.idGenerator = new UniqueIdGenerator();
                    CFACreator cfaCreator = new CFACreator(config, logger, shutdownNotifier);
                    CFA cfaForComparison =
                        cfaCreator.parseFileAndCreateCFA(ImmutableList.of(originalProgram.toString()));
                    ImpactedDiffer.getInstance().cfadiff(cfaForComparison, cfa, logger);
                    stats.cfadiffTime.stop();
                } else if(ImpactedHelper.getInstance().cfaInfoPath != null) {
                    try {
                        ImpactedDiffer.getInstance().cfadiff_external();
                    } catch (IOException e) {
                        e.printStackTrace();
                        System.exit(-1);
                    }
                }

                stats.impacted_traverse_new_Time.start();
                // decide the initial affected variables
                ImpactedCFAUtils.traverse_new(cfa);
                ImpactedCFAUtils.handleDeletedEdges();
                stats.impacted_traverse_new_Time.stop();

                long start0 = -1;
                try {
                    start0 = ProcessCpuTime.read();
                } catch (JMException pE) {
                    pE.printStackTrace();
                }
                // start = mxBean.getCurrentThreadCpuTime();
                if(ImpactedHelper.getInstance().maxImpactedNum > 0) {
                    CPAMain.isIncPred = false;
                    Configuration impactedConfig = CPAMain.impactedConfig;

//                    MainCPAStatistics impactedStats = new MainCPAStatistics(impactedConfig, logger);

                    CoreComponentsFactory impactedFactory =
                        new CoreComponentsFactory(impactedConfig, logger,
                            shutdownNotifier);
                    ConfigurableProgramAnalysis impactedCPA = impactedFactory.createCPA(
                        cfa, stats,
                        speComposition);
                    GlobalInfo.getInstance().storeCPA(impactedCPA);
                    Algorithm algorithm_impacted = impactedFactory.createAlgorithm(impactedCPA,
                        programDenotation, cfa, stats);
                    ReachedSet impactedReached;
                    ImpactedHelper.getInstance().isFixed = false;
                    int count = 1;
                    while(!ImpactedHelper.getInstance().isFixed) {
                        // System.out.println("iter " + count++);
                        ImpactedHelper.getInstance().isFixed = true;
                        impactedReached =
                            initializeReachedSet(impactedFactory.createReachedSet(), impactedCPA, cfa.getMainFunction(), cfa);
                        runAlgorithm0(algorithm_impacted, impactedReached);
                    }
//                    impactedReached =
//                        initializeReachedSet(impactedFactory.createReachedSet(), impactedCPA, cfa.getMainFunction(), cfa);
//                    runAlgorithm(algorithm_impacted, impactedReached, impactedStats);
                    CPAMain.isIncPred = true;
                    // ModificationsCPA.finish = true;
                }
                long end0 = -1;
                try {
                    end0 = ProcessCpuTime.read();
                } catch (JMException pE) {
                    pE.printStackTrace();
                }
                // end = mxBean.getCurrentThreadCpuTime();
                impactedCpuTime = end0 - start0;

                ImpactedHelper.getInstance().readyForAnalysis = true;
                System.out.println("Begin analysis ");
                GlobalInfo.getInstance().storeCFA(cfa);
                shutdownNotifier.shutdownIfNecessary();

                ConfigurableProgramAnalysis cpa = factory.createCPA(
                        cfa, stats,
                        speComposition);
                GlobalInfo.getInstance().storeCPA(cpa);

                algorithm = factory.createAlgorithm(cpa, programDenotation, cfa, stats);

                if (algorithm instanceof ImpactAlgorithm) {
                    ImpactAlgorithm mcmillan = (ImpactAlgorithm)algorithm;
                    reached.add(mcmillan.getInitialState(cfa.getMainFunction()), mcmillan.getInitialPrecision(cfa.getMainFunction()));
                } else {
                    ImpactedHelper.getInstance().loadInvariantFromFile();
                    reached = initializeReachedSet(reached, cpa, cfa.getMainFunction(), cfa);
                }
            }

            ImpactedHelper.getInstance().initialReachedSize = reached.size();

            printConfigurationWarnings();

            stats.creationTime.stop();
            shutdownNotifier.shutdownIfNecessary();
            // now everything necessary has been instantiated

            if (disableAnalysis) {
                return new CPAcheckerResult(Result.NOT_YET_STARTED,
                        violatedPropertyDescription, null, stats);
            }

            // run analysis
            result = Result.UNKNOWN; // set to unknown so that the result is correct in case of exception

            AlgorithmStatus status = null;

            long start = -1;
            try {
                start = ProcessCpuTime.read();
            } catch (JMException pE) {
                pE.printStackTrace();
            }
            // start = mxBean.getCurrentThreadCpuTime();
            if(IncrementalPAUtil.getInstance().reached == null){
                IncrementalPAUtil.isInit = false;
                status = runAlgorithm(algorithm, reached, stats);
            } else {
                status = runAlgorithm(algorithm, IncrementalPAUtil.getInstance().reached, stats);
            }
            long end = -1;
            try {
                end = ProcessCpuTime.read();
            } catch (JMException pE) {
                pE.printStackTrace();
            }
            // end = mxBean.getCurrentThreadCpuTime();
            normalanalysisCpuTime = end - start;

            violatedPropertyDescription = findViolatedProperties(reached);
            // if (violatedPropertyDescription != null && !violatedPropertyDescription.equals("")) {
            if (violatedPropertyDescription != null) {
                if (!status.isPrecise()) {
                    result = Result.UNKNOWN;
                } else {
                    System.out.println("violated property description: " + violatedPropertyDescription);
                    result = Result.FALSE;
                }
            } else {
                violatedPropertyDescription = "";
                result = analyzeResult(reached, status.isSound());
                if (unknownAsTrue && result == Result.UNKNOWN) {
                    GlobalInfo.getInstance().result = result;
                    result = Result.TRUE;
                }
            }

            if (unknownAsTrue && result == Result.UNKNOWN) {
                GlobalInfo.getInstance().result = result;
                result = Result.TRUE;
            }

        } catch (IOException e) {
            logger.logUserException(Level.SEVERE, e, "Could not read file");

        } catch (ParserException e) {
            logger.logUserException(Level.SEVERE, e, "Parsing failed");
            StringBuilder msg = new StringBuilder();
            msg.append("Please make sure that the code can be compiled by a compiler.\n");
            if (e.getLanguage() == Language.C) {
                msg.append("If the code was not preprocessed, please use a C preprocessor\nor specify the -preprocess command-line argument.\n");
            }
            msg.append("If the error still occurs, please send this error message\ntogether with the input file to cpachecker-users@googlegroups.com.\n");
            logger.log(Level.INFO, msg);

        } catch (InvalidConfigurationException e) {
            logger.logUserException(Level.SEVERE, e, "Invalid configuration");

        } catch (InterruptedException e) {
            // CPAchecker must exit because it was asked to
            // we return normally instead of propagating the exception
            // so we can return the partial result we have so far
            if (!Strings.isNullOrEmpty(e.getMessage())) {
                logger.logUserException(Level.WARNING, e, "Analysis stopped");
            }

        } catch (CPAException e) {
            logger.logUserException(Level.SEVERE, e, null);

        } finally {
            shutdownNotifier.unregister(interruptThreadOnShutdown);
        }
        return new CPAcheckerResult(result,
                violatedPropertyDescription, reached, stats);
    }

    private void checkIfOneValidFile(String fileDenotation) throws InvalidConfigurationException {
        if (!denotesOneFile(fileDenotation)) {
            throw new InvalidConfigurationException(
                    "Exactly one code file has to be given.");
        }

        Path file = Paths.get(fileDenotation);

        try {
            Files.checkReadableFile(file);
        } catch (FileNotFoundException e) {
            throw new InvalidConfigurationException(e.getMessage());
        }
    }

    private boolean denotesOneFile(String programDenotation) {
        return !programDenotation.contains(",");
    }

    private CFA parse(String fileNamesCommaSeparated, MainCPAStatistics stats) throws InvalidConfigurationException, IOException,
            ParserException, InterruptedException {
        // parse file and create CFA
        CFACreator cfaCreator = new CFACreator(config, logger, shutdownNotifier);
        stats.setCFACreator(cfaCreator);

        Splitter commaSplitter = Splitter.on(',').omitEmptyStrings().trimResults();
        CFA cfa = cfaCreator.parseFileAndCreateCFA(commaSplitter.splitToList(fileNamesCommaSeparated));
        stats.setCFA(cfa);
        return cfa;
    }

    private void printConfigurationWarnings() {
        Set<String> unusedProperties = config.getUnusedProperties();
        if (!unusedProperties.isEmpty()) {
            logger.log(Level.WARNING, "The following configuration options were specified but are not used:\n",
                    Joiner.on("\n ").join(unusedProperties), "\n");
        }
        Set<String> deprecatedProperties = config.getDeprecatedProperties();
        if (!deprecatedProperties.isEmpty()) {
            logger.log(Level.WARNING, "The following options are deprecated and will be removed in the future:\n",
                    Joiner.on("\n ").join(deprecatedProperties), "\n");
        }
    }

    private AlgorithmStatus runAlgorithm(final Algorithm algorithm,
                                         final ReachedSet reached,
                                         final MainCPAStatistics stats) throws CPAException,
                                                                               InterruptedException, IOException {

        logger.log(Level.INFO, "Starting analysis ...");

        AlgorithmStatus status = AlgorithmStatus.SOUND_AND_PRECISE;

        // register management interface for CPAchecker
        CPAcheckerBean mxbean = new CPAcheckerBean(reached, logger, shutdownNotifier);

        stats.startAnalysisTimer();
        try {

            do {
                status = status.update(algorithm.run(reached));

                // either run only once (if stopAfterError == true)
                // or until the waitlist is empty
            } while (!stopAfterError && reached.hasWaitingState());

            logger.log(Level.INFO, "Stopping analysis ...");
            return status;

        } finally {
            stats.stopAnalysisTimer();

            // unregister management interface for CPAchecker
            mxbean.unregister();
        }
    }

    private void runAlgorithm0(final Algorithm algorithm,
                                         final ReachedSet reached) throws CPAException,
                                                                               InterruptedException {
        do {
            algorithm.run(reached);
        } while (!stopAfterError && reached.hasWaitingState());

    }


    private @Nullable String findViolatedProperties(final ReachedSet reached) {
        Set<String> descriptions = from(reached).filter(IS_TARGET_STATE)
                .transform(new Function<AbstractState, String>() {
                    @Override
                    public String apply(AbstractState s) {
                        return  ((Targetable)s).getViolatedPropertyDescription();
                    }
                })
                .copyInto(new HashSet<String>());
        if (descriptions.isEmpty()) {
            // signal no target state -> result safe
            return null;
        }
        descriptions.remove("");
        return Joiner.on(", ").join(descriptions);
    }

    private Result analyzeResult(final ReachedSet reached, boolean isSound) {
        if (reached.hasWaitingState()) {
            logger.log(Level.WARNING, "Analysis not completed: there are still states to be processed.");
            return Result.UNKNOWN;
        }

        if (!isSound) {
            logger.log(Level.WARNING, "Analysis incomplete: no errors found, but not everything could be checked.");
            return Result.UNKNOWN;
        }

        return Result.TRUE;
    }

    private void addToInitialReachedSet(
            final Set<? extends CFANode> pLocations,
            final Object pPartitionKey,
            final ReachedSet pReached,
            final ConfigurableProgramAnalysis pCpa) {

        for (CFANode loc: pLocations) {
            StateSpacePartition putIntoPartition = partitionInitialStates
                    ? StateSpacePartition.getPartitionWithKey(pPartitionKey)
                    : StateSpacePartition.getDefaultPartition();

            AbstractState initialState = pCpa.getInitialState(loc, putIntoPartition);
            Precision initialPrecision = pCpa.getInitialPrecision(loc, putIntoPartition);

            pReached.add(initialState, initialPrecision);
        }
    }
    private void addToInitialReachedSetByInvPreventBot(
        final Set<? extends CFANode> pLocations,
        final Object pPartitionKey,
        final ReachedSet reachedSet,
        final ConfigurableProgramAnalysis cpa,
        final CFA pCfa) throws CPAException, InterruptedException {

        HashMap<Integer, CFANode> int2CfaNode = new HashMap<>();
        for(CFANode n : pCfa.getAllNodes()) {
            Integer num = n.getNodeNumber();
            int2CfaNode.put(num, n);
        }

        long startInit = -1;
        try {
            startInit = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }

        for (CFANode loc: pLocations) {
            StateSpacePartition putIntoPartition = partitionInitialStates
                                                   ? StateSpacePartition
                                                       .getPartitionWithKey(pPartitionKey)
                                                   : StateSpacePartition.getDefaultPartition();

            AbstractState initialState = cpa.getInitialState(loc, putIntoPartition);
            Precision initialPrecision = cpa.getInitialPrecision(loc, putIntoPartition);

            if(ImpactedHelper.getInstance().extractInitialPrec){
                for (Precision p : ((CompositePrecision) initialPrecision).getWrappedPrecisions()) {
                    if (p instanceof PredicatePrecision) {
                        if (p.toString().equals("empty")) {
                            for (Map.Entry m :
                                ImpactedHelper.getInstance().lastVFileDisjInvariants.entrySet()) {
                                Pair<PredicatePrecision, AbstractionFormula> pair =
                                    (Pair<PredicatePrecision, AbstractionFormula>) m.getValue();
                                Integer locNum = (Integer) m.getKey();
                                CFANode node = int2CfaNode.get(locNum);
                                if (node == null) {
                                    continue;
                                }
                                Collection<AbstractionPredicate> addedPredicates = new HashSet<>();
                                pCfa.getAllNodes();
                                BooleanFormula instantiatedFormula =
                                    pair.getSecond().asInstantiatedFormula();
                                if (instantiatedFormula.toString().equals("true"))
                                    continue;
                                addedPredicates.addAll(GlobalInfo.getInstance().predicateManager
                                    .extractPredicates(instantiatedFormula));

                                if (GlobalInfo.getInstance().predicateSharing
                                    == PredicateSharing.FUNCTION) {
                                    Multimap<String, AbstractionPredicate> newFuncPredicates =
                                        ArrayListMultimap.create();
                                    newFuncPredicates
                                        .putAll(node.getFunctionName(), addedPredicates);
                                    GlobalInfo.getInstance().predicateCPA.initialPrecision =
                                        GlobalInfo.getInstance().predicateCPA.initialPrecision
                                            .addFunctionPredicates(newFuncPredicates);
                                    GlobalInfo.getInstance().predicateCPA.initialPrecision =
                                        GlobalInfo.getInstance().predicateCPA.initialPrecision
                                            .addGlobalPredicates(addedPredicates);
                                } else if (GlobalInfo.getInstance().predicateSharing
                                    == PredicateSharing.GLOBAL) {
                                    GlobalInfo.getInstance().predicateCPA.initialPrecision =
                                        GlobalInfo.getInstance().predicateCPA.initialPrecision
                                            .addGlobalPredicates(addedPredicates);
                                }


                            }
                            initialPrecision = cpa.getInitialPrecision(loc, putIntoPartition);
                        }
                    }
                }
            }
            reachedSet.add(initialState, initialPrecision);
            ImpactedHelper.getInstance().bestPrecisionPerFunction =
                Precisions.extractPrecisionByType(initialPrecision, PredicatePrecision.class);
        }
        long endInit = -1;
        try {
            endInit = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        cputimePrec = endInit - startInit;

        final TransferRelation transferRelation = cpa.getTransferRelation();
        final MergeOperator mergeOperator = cpa.getMergeOperator();
        final StopOperator stopOperator = cpa.getStopOperator();
        final PrecisionAdjustment precisionAdjustment =
            cpa.getPrecisionAdjustment();

        while (reachedSet.hasWaitingState()) {


            // Pick next state using strategy
            // BFS, DFS or top sort according to the configuration

            final AbstractState state = reachedSet.popFromWaitlist();
            final Precision precision = reachedSet.getPrecision(state);

//            System.out.println(AbstractStates.extractStateByType(state, LocationState.class).getLocationNode().toString() + ": " +
//                AbstractStates.extractStateByType(state, ImpactedState.class).getImpactedVariables().toString());

            logger.log(Level.FINER, "Retrieved state from waitlist");
            logger.log(Level.ALL, "Current state is", state, "with precision",
                precision);

//            if (forcedCovering != null) {
//                try {
//                    boolean stop = forcedCovering.tryForcedCovering(state, precision, reachedSet);
//
//                    if (stop) {
//                        // TODO: remove state from reached set?
//                        continue;
//                    }
//                } finally {
//                }
//            }

            Collection<? extends AbstractState> successors;

            successors = transferRelation.getAbstractSuccessors(state, precision);

            // TODO When we have a nice way to mark the analysis result as incomplete,
            // we could continue analysis on a CPATransferException with the next state from waitlist.

            int numSuccessors = successors.size();
            logger.log(Level.FINER, "Current state has", numSuccessors,
                "successors");

            for (AbstractState successor : Iterables.consumingIterable(successors)) {
                logger.log(Level.FINER, "Considering successor of current state");
                logger.log(Level.ALL, "Successor of", state, "\nis", successor);

                PrecisionAdjustmentResult precAdjustmentResult;
                IncrementalPAUtil.getInstance().prevLoc = extractLocation(state).getNodeNumber();
                Optional<PrecisionAdjustmentResult> precAdjustmentOptional =
                    precisionAdjustment.prec(
                        successor, precision, reachedSet,
                        Functions.<AbstractState>identity(),
                        successor);

                if (!precAdjustmentOptional.isPresent()) {
                    continue;
                }
                precAdjustmentResult = precAdjustmentOptional.get();


                successor = precAdjustmentResult.abstractState();
                Precision successorPrecision = precAdjustmentResult.precision();
                Action action = precAdjustmentResult.action();

                if (action == Action.BREAK) {
                    boolean stop;

                    stop = stopOperator.stop(successor, reachedSet.getReached(successor), successorPrecision);


                    if (AbstractStates.isTargetState(successor) && stop) {
                        // don't signal BREAK for covered states
                        // no need to call merge and stop either, so just ignore this state
                        // and handle next successor
                        logger.log(Level.FINER,
                            "Break was signalled but ignored because the state is covered.");
                        continue;

                    } else {
                        logger.log(Level.FINER, "Break signalled, CPAAlgorithm will stop.");

                        // add the new state
                        reachedSet.add(successor, successorPrecision);

                        if (!successors.isEmpty()) {
                            // re-add the old state to the waitlist, there are unhandled
                            // successors left that otherwise would be forgotten
                            reachedSet.reAddToWaitlist(state);
                        }
                        return;

                    }
                }
                assert action == Action.CONTINUE : "Enum Action has unhandled values!";

                Collection<AbstractState> reached = reachedSet.getReached(successor);

                // An optimization, we don't bother merging if we know that the
                // merge operator won't do anything (i.e., it is merge-sep).
                if (mergeOperator != MergeSepOperator.getInstance() && !reached.isEmpty()) {
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
                    }
                }

                boolean stop;

                stop = stopOperator.stop(successor, reached, successorPrecision);


                if (stop) {
                    logger.log(Level.FINER,
                        "Successor is covered or unreachable, not adding to waitlist");
                } else {
                    logger.log(Level.FINER,
                        "No need to stop, adding successor to waitlist");

                    reachedSet.add(successor, successorPrecision);

                    PredicateAbstractState abs = AbstractStates.extractStateByType(successor,
                        PredicateAbstractState.class);
                    if(state == reachedSet.getFirstState()) {
                        IncrementalPAUtil.getInstance().waitSet.add(Triple.of(state, precision,
                            -1));
                    }
                    // if(!abs.getAbstractionFormula().isFalse() && !((ARGState) successor)
                    // .isTarget()) {
//                    if(!abs.getAbstractionFormula().isFalse() && abs.isAbstractionState() && !((ARGState) successor).isTarget()) {
//                        IncrementalPAUtil.getInstance().waitSet.add(Triple.of(successor, successorPrecision,
//                            1));
//                    }
                    if(!abs.getAbstractionFormula().isFalse() && !((ARGState) successor).isTarget()) {
                        IncrementalPAUtil.getInstance().waitSet.add(Triple.of(successor, successorPrecision,
                            1));
                    }
                }
            }

//            if (iterationListener != null) {
//                iterationListener.afterAlgorithmIteration(this, reachedSet);
//            }
        }
    }

    private ReachedSet initializeReachedSet(
            ReachedSet pReached,
            final ConfigurableProgramAnalysis pCpa,
            final FunctionEntryNode pAnalysisEntryFunction,
            final CFA pCfa) throws InvalidConfigurationException {

        logger.log(Level.FINE, "Creating initial reached set");

        for (InitialStatesFor isf: initialStatesFor) {
            final ImmutableSet<? extends CFANode> initialLocations;
            switch (isf) {
                case ENTRY:
                    initialLocations = ImmutableSet.of(pAnalysisEntryFunction);
                    break;
                case EXIT:
                    initialLocations = ImmutableSet.of(pAnalysisEntryFunction.getExitNode());
                    break;
                case FUNCTION_ENTRIES:
                    initialLocations = ImmutableSet.copyOf(pCfa.getAllFunctionHeads());
                    break;
                case FUNCTION_SINKS:
                    initialLocations = ImmutableSet.<CFANode>builder().addAll(getAllEndlessLoopHeads(pCfa.getLoopStructure().get()))
                            .addAll(getAllFunctionExitNodes(pCfa))
                            .build();
                    break;
                case PROGRAM_SINKS:
                    Builder<CFANode> builder = ImmutableSet.<CFANode>builder().addAll(getAllEndlessLoopHeads(pCfa.getLoopStructure().get()));
                    if (pCfa.getAllNodes().contains(pAnalysisEntryFunction.getExitNode())) {
                        builder.add(pAnalysisEntryFunction.getExitNode());
                    }
                    initialLocations = builder.build();
                    break;
                case TARGET:
                    TargetLocationProvider tlp = new TargetLocationProvider(factory.getReachedSetFactory(), shutdownNotifier, logger, config, pCfa);
                    initialLocations = tlp.tryGetAutomatonTargetLocations(pAnalysisEntryFunction);
                    break;
                default:
                    throw new AssertionError("Unhandled case statement: " + initialStatesFor);
            }

            if(CPAMain.isIncPred) {
                try {
                    // yqs17: example simple: false to true, need to add this line of code
                    // ImpactedHelper.getInstance().lastVFileDisjInvariants.remove(18);
                    long startInit = -1;
                    try {
                        startInit = ProcessCpuTime.read();
                    } catch (JMException pE) {
                        pE.printStackTrace();
                    }
                    if(ImpactedHelper.getInstance().lastVFileInvariants.size() != 0 || ImpactedHelper.getInstance().lastVFileDisjInvariants.size() != 0) {
                        ImpactedHelper.lastInvs =
                            ImpactedHelper.getInstance().lastVFileDisjInvariants.size();
                        addToInitialReachedSetByInvPreventBot(initialLocations, isf, pReached, pCpa,
                            pCfa);
                    }
                    long endInit = -1;
                    try {
                        endInit = ProcessCpuTime.read();
                    } catch (JMException pE) {
                        pE.printStackTrace();
                    }
                    cputimeInit = endInit - startInit;
                    if(ImpactedHelper.hits != 0) {
                        pReached = IncrementalPAUtil.getInstance().setReached(pReached);
                        IncrementalPAUtil.isInit = false;
                        if (argFile != null) {
                            final Set<Pair<ARGState, ARGState>> allTargetPathEdges = new HashSet<>();
                            try (Writer w = Files.openOutputFile(argFile)) {
                                ARGToDotWriter.write(w, (ARGState) pReached.getFirstState(),
                                    ARGUtils.CHILDREN_OF_STATE,
                                    Predicates.alwaysTrue(),
                                    Predicates.in(allTargetPathEdges));
                            } catch (IOException e) {
                                System.out.println("Could not write initial "
                                    + "ARG to file");
                                throw new UnsupportedOperationException("Could not write initial "
                                    + "ARG to file");
                            }
                        }

                    } else {
                        if(!ImpactedHelper.getInstance().extractInitialPrec && GlobalInfo.getInstance().predicateCPA != null) {
                            GlobalInfo.getInstance().predicateCPA.initialPrecision =
                                GlobalInfo.getInstance().emptyPrecision;
                        }
                        pReached = ImpactedHelper.getInstance().factory.createReachedSet();
                        ImpactedHelper.getInstance().invariantsFile = Paths.get("null.txt");
                        CPAMain.isReuseInvariant = false;
                        IncrementalPAUtil.isInit = false;
                        ImpactedHelper.getInstance().lastVFileDisjInvariants.clear();
                        addToInitialReachedSet(initialLocations, isf, pReached, pCpa);
                        pReached = ImpactedHelper.getInstance().factory.createReachedSet();
                        CPAMain.isIncPred = false;
                        IncrementalPAUtil.isInit = false;
                        addToInitialReachedSet(initialLocations, isf, pReached, pCpa);
                    }
                } catch (InterruptedException ie) {
                    ie.printStackTrace();
                } catch (CPAException ce) {
                    // ce.printStackTrace();
                } finally {
//                    long endInit = -1;
//                    try {
//                        endInit = ProcessCpuTime.read();
//                    } catch (JMException pE) {
//                        pE.printStackTrace();
//                    }
//                    cputimeInit = endInit - startInit;
//                    if(ImpactedHelper.hits == 0) {
//                        cputimeInit = 0;
//                    }

                }
            } else {
                addToInitialReachedSet(initialLocations, isf, pReached, pCpa);
            }
        }

        if (!pReached.hasWaitingState() && !CPAMain.isIncPred) {
            throw new InvalidConfigurationException("Initialization of the set of initial states failed: No analysis target found!");
        }

        return pReached;
    }

    private Set<CFANode> getAllFunctionExitNodes(CFA cfa) {
        Set<CFANode> functionExitNodes = new HashSet<>();

        for (FunctionEntryNode node : cfa.getAllFunctionHeads()) {
            FunctionExitNode exitNode = node.getExitNode();
            if (cfa.getAllNodes().contains(exitNode)) {
                functionExitNodes.add(exitNode);
            }
        }
        return functionExitNodes;
    }

    private Set<CFANode> getAllEndlessLoopHeads(LoopStructure structure) {
        ImmutableCollection<Loop> loops = structure.getAllLoops();
        Set<CFANode> loopHeads = new HashSet<>();

        for (Loop l : loops) {
            if (l.getOutgoingEdges().isEmpty()) {
                // one loopHead per loop should be enough for finding all locations
                for (CFANode head : l.getLoopHeads()) {
                    loopHeads.add(head);
                }
            }
        }
        return loopHeads;
    }
}
