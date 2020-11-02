package org.sosy_lab.cpachecker.cpa.impacted;

import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.google.common.collect.Queues;
import com.google.common.collect.Sets;
import java.io.ByteArrayOutputStream;
import java.io.FilterOutputStream;
import java.util.zip.GZIPOutputStream;
import javax.management.JMException;
import org.anarres.parallelgzip.ParallelGZIPOutputStream;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.Triple;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.Paths;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.PrecisionHelpState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.PredicateAnalysisPrecisionExtractor;
import org.sosy_lab.cpachecker.cpa.callstack.CallstackState;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.Precisions;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;
import org.sosy_lab.cpachecker.util.predicates.interfaces.RegionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.*;
import org.sosy_lab.cpachecker.util.resources.ProcessCpuTime;

import static com.google.common.base.MoreObjects.firstNonNull;
import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.cpachecker.util.AbstractStates.extractLocation;


public class InvariantsWriter {

    private final LogManager logger;
    private final FormulaManagerView fmgr;
    private final AbstractionManager absmgr;
    private final RegionManager rmgr;
    private Map<Pair<Integer, String>, AbstractState> curVMemoryInvariants = new HashMap<>();
    private Map<Integer, Pair<PredicatePrecision, AbstractionFormula>> curVMemoryDisjInvariants =
        new HashMap<>();
    private Map<Integer, Pair<Region, BooleanFormula>> curVMemoryDisjRegions =
        new HashMap<>();
    private final ImpactedCPA cpa;

    final Timer invWriteTimer = new Timer();
    final Timer invCollectTimer = new Timer();
    final Timer invCollectMergeTimer = new Timer();
    final Timer invCollectRegionTimer = new Timer();
    final Timer invCollectPrecTimer = new Timer();
    final Timer invCollectPathFormulaTimer = new Timer();

    int serializeCount = 0;

    public InvariantsWriter(LogManager pLogger, AbstractionManager pAbsMgr,
                            FormulaManagerView pFmMgr, RegionManager pRegMgr, ImpactedCPA cpa) {
        this.logger = pLogger;
        this.absmgr = pAbsMgr;
        this.fmgr = pFmMgr;
        this.rmgr = pRegMgr;
        this.cpa = cpa;
    }

    private static final Predicate<AbstractState> IS_ABSTRACTION_STATE = new Predicate<AbstractState>() {
        @Override
        public boolean apply(AbstractState pArg0) {
            PredicateAbstractState e = AbstractStates.extractStateByType(pArg0, PredicateAbstractState.class);
            return e.isAbstractionState();
        }
    };

    public int getOutputInvCount() {
        if(ImpactedHelper.getInstance().isInvDisj) {
            if(curVMemoryDisjRegions.size() != 0) {
                return curVMemoryDisjRegions.size();
            }
            return curVMemoryDisjInvariants.size();
        } else {
            return curVMemoryInvariants.size();
        }
    }

    private int getAbstractionId(ARGState state) {
        PredicateAbstractState paState = AbstractStates.extractStateByType(state, PredicateAbstractState.class);
        return paState.getAbstractionFormula().getId();
    }

    void writeInvariantsSimple(Path invariantsFile) {
        invCollectTimer.start();
        try {
            ImpactedCPAStatistics.invCollectCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }

        try {
            ImpactedCPAStatistics.invWriteCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        invWriteTimer.start();

        Map<CFANode, Region> regions = IncrementalPAUtil.getInstance().regions;
        for (CFANode node : regions.keySet()) {
            Integer loc = node.getNodeNumber();
            if(ImpactedHelper.getInstance().allFunctionNames.containsKey(node.getFunctionName()))
                ImpactedHelper.getInstance().allFunctionNames.remove(node.getFunctionName());
            Region region = regions.get(node);
            BooleanFormula formula = absmgr.toConcrete(region);
            curVMemoryDisjRegions.put(loc, Pair.of(region, formula));
        }

        long stopCpuTime = 0;
        try {
            stopCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        ImpactedCPAStatistics.invCollectCpuTime =
            stopCpuTime - ImpactedCPAStatistics.invCollectCpuTime;
        invCollectTimer.stop();

        try (FileOutputStream fileWriter = new FileOutputStream(invariantsFile.toFile());
             FilterOutputStream gzipO = ImpactedHelper.getInstance().parallelOutput ? new ParallelGZIPOutputStream(fileWriter) : new GZIPOutputStream(fileWriter);
             ObjectOutputStream objO = ImpactedHelper.getInstance().compressIO ? new ObjectOutputStream(gzipO) : new ObjectOutputStream(fileWriter)) {
                for(Map.Entry<Integer, Pair<Region, BooleanFormula>> curEntry :
                    curVMemoryDisjRegions.entrySet()) {
                    String locStr = "" + curEntry.getKey().toString();

                        try {
                            serializeCount += 1;
                            objO.writeObject(locStr);
                            //TODO qianshan CFANode cannot be serialized
                            checkArgument(curEntry.getValue() != null);
                            Region region = curEntry.getValue().getFirst();
                            BooleanFormula formula = curEntry.getValue().getSecond();
                            PathFormulaManager pfm =
                                GlobalInfo.getInstance().getPathFormulaManager();
                            AbstractionFormula absFormula = new AbstractionFormula(GlobalInfo.getInstance().getFormulaManagerView(),
                                region, formula, formula,
                                pfm.makeEmptyPathFormula(), ImmutableSet.of());
                            //objO.writeObject(curEntry.getValue().getFirst());
                            objO.writeObject(absFormula);

                        } catch (IOException e) {
                            e.printStackTrace();
                            System.out.println("serialization error");
                        }
                }

                if(CPAMain.result.getResult().name().equals("TRUE")) {
                    for (FunctionEntryNode unreachFuncEntry :
                        ImpactedHelper.getInstance().allFunctionNames.values()) {
                        String locStr = "" + unreachFuncEntry.getNodeNumber();
                        try {
                            serializeCount += 1;
                            objO.writeObject(locStr);
                            //TODO qianshan CFANode cannot be serialized
                            Region region = GlobalInfo.getInstance().getRegionManager().makeFalse();
                            BooleanFormula formula =
                                GlobalInfo.getInstance().getSmtInterpolBooleanFormulaManager()
                                    .makeBoolean(false);
                            PathFormulaManager pfm =
                                GlobalInfo.getInstance().getPathFormulaManager();
                            AbstractionFormula absFormula = new AbstractionFormula(
                                GlobalInfo.getInstance().getFormulaManagerView(),
                                region, formula, formula,
                                pfm.makeEmptyPathFormula(), ImmutableSet.of());
                            //objO.writeObject(curEntry.getValue().getFirst());
                            objO.writeObject(absFormula);
                        } catch (IOException e) {
                            e.printStackTrace();
                            System.out.println("serialization error");
                        }
                    }
                }


                objO.writeObject(null);

        } catch (Exception e) {
            // TODO Auto-generated catch block
            System.out.println("serialization error");
        }

        stopCpuTime = 0;
        try {
            stopCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        invWriteTimer.stop();
        ImpactedCPAStatistics.invWriteCpuTime = stopCpuTime - ImpactedCPAStatistics.invWriteCpuTime;

    }

    void writeInvariants(Path invariantsFile, ReachedSet reached) {
        invCollectTimer.start();

        // in this set, we collect the string representing each predicate
        // (potentially making use of the above definitions)
        //Map<ARGState, String> stateToAssert = Maps.newHashMap();
        Map<Integer, PredicateAbstractState> locToState = Maps.newHashMap();

        // Get list of all abstraction states in the set reached
        ARGState rootState = AbstractStates.extractStateByType(reached.getFirstState(), ARGState.class);
        //SetMultimap<ARGState, ARGState> successors = ARGUtils.projectARG(rootState, ARGUtils.CHILDREN_OF_STATE, IS_ABSTRACTION_STATE);

        Set<ARGState> done = Sets.newHashSet();
        Deque<ARGState> worklist = Queues.newArrayDeque();

        worklist.add(rootState);

        ArrayList<Integer> locs = new ArrayList<>();
        Map<Integer, Triple<PredicatePrecision, PathFormula, Region>> invariants = Maps.newHashMap();


        while (!worklist.isEmpty()) {
            ARGState state = worklist.pop();

            // System.out.println("output invariant..." + state.getStateId());
            // System.out.println(done.size() + " visited");
//                if(state.isCovered()) {
//                    continue;
//                }
            CompositeState comp = (CompositeState) state.getWrappedState();
            List<AbstractState> comps = comp.getWrappedStates();
            String funName = null;
            PredicateAbstractState pState = null;
            Integer locNum = -1;
            Integer loc = (extractLocation(state)).getNodeNumber();
            for(AbstractState s : comps) {
                if(s instanceof CallstackState){
                    funName = ((CallstackState) s ).getCurrentFunction();
                }
                if(s instanceof PredicateAbstractState) {
                    pState = (PredicateAbstractState) s;
                }
                if(s instanceof LocationState) {
                    locNum = ((LocationState) s).getLocationNode().getNodeNumber();
                }
            }



            if (done.contains(state)) {
                continue;
            }
            if (!pState.isAbstractionState()) {
                worklist.addAll(state.getChildren());
                done.add(state);
                continue;
            }
            //children = (List<ARGState>) state.getChildren();
            // Handle successors
            worklist.addAll(state.getChildren());

            // Abstraction formula
            //BooleanFormula formula = pState.getAbstractionFormula().asFormula();

            //Pair<String, List<String>> p = splitFormula(fmgr, formula);
            //String formulaString = p.getFirst();


            //stateToAssert.put(state, formulaString);
            if(!state.isCovered() && !ImpactedHelper.getInstance().isInvDisj) {
                //Precisions.extractPrecisionByType(reached.getPrecision(state), PredicatePrecision.class);
                PrecisionHelpState curPHState =
                        new PrecisionHelpState(funName, reached.getPrecision(state), new PredicateAnalysisPrecisionExtractor());
                curVMemoryInvariants.put(Pair.of(locNum, curPHState.toString()), pState);
            } else if(!state.isCovered() && ImpactedHelper.getInstance().isInvDisj) {
                //PredicatePrecision prec = Precisions.extractPrecisionByType(reached.getPrecision(state), PredicatePrecision.class);
                Triple<PredicatePrecision, PathFormula, Region> invariant = invariants.get(loc);
                PredicatePrecision prec = null;
                PathFormula pathFormula = null;
                Region region = null;
                if(invariant != null) {
                    prec = invariant.getFirst();
                    pathFormula = invariant.getSecond();
                    region = invariant.getThird();
                }

                PathFormula curPathFormula = pState.getPathFormula();

                try {
                    if(pathFormula == null) {
                        pathFormula = curPathFormula;
                    } else {
                        invCollectMergeTimer.start();
                        invCollectPathFormulaTimer.start();
                        if(ImpactedHelper.getInstance().aggressive_pathformula) {
                            pathFormula = GlobalInfo.getInstance().getPathFormulaManager().makeOrLight(pathFormula, curPathFormula);
                        } else {
                            pathFormula = GlobalInfo.getInstance().getEmptyPathFormula();
                        }
                        invCollectPathFormulaTimer.stop();
                        invCollectMergeTimer.stop();
                    }
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }

                region = firstNonNull(region, rmgr.makeFalse());
                PredicatePrecision curPrec = Precisions.extractPrecisionByType(reached.getPrecision(state), PredicatePrecision.class);
                Region curRegion = pState.getAbstractionFormula().asRegion();
                if(prec == null) {
                    prec = curPrec;
                } else {
                    invCollectMergeTimer.start();
                    invCollectPrecTimer.start();
                    if(!(prec == null || curPrec == null)) {
                        //System.out.println("Inv Writer: prec extention");
                        prec = prec.mergeWith(curPrec);
                    }
                    invCollectPrecTimer.stop();
                    invCollectMergeTimer.stop();
                }

                invCollectMergeTimer.start();
                invCollectRegionTimer.start();
                region = rmgr.makeOr(region, curRegion);
                invCollectRegionTimer.stop();
                invCollectMergeTimer.stop();

                if(!locs.contains(loc))
                    locs.add(loc);
                if(invariants.containsKey(loc)) {
                    //System.out.println("Invariant exists");
                    if(prec == null || prec.getLocalPredicates() == null) {
                        continue;
                    }
                    ImmutableSet<AbstractionPredicate> toAddedPredicates = prec.getLocalPredicates().get(extractLocation(state));
                    ImmutableSet<AbstractionPredicate> existedPredicates;
                    try {
                        existedPredicates = invariants.get(loc).getFirst().getLocalPredicates()
                            .get(extractLocation(state));
                    } catch (NullPointerException npe) {
                        continue;
                    }
                    if(toAddedPredicates.size() > existedPredicates.size()) {
                        invariants.put(loc, Triple.of(prec, pathFormula, region));
                        System.out.println("Renew invariant");
                        locToState.put(loc, pState);
                    }
                } else {
                    invariants.put(loc, Triple.of(prec, pathFormula, region));
                    //System.out.println("Renew invariant");
                    locToState.put(loc, pState);
                }
            }
            done.add(state);
        }

        long stopCpuTime = 0;
        try {
            stopCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        ImpactedCPAStatistics.invCollectCpuTime = stopCpuTime - ImpactedCPAStatistics.invCollectCpuTime;
        invCollectTimer.stop();

        try {
            ImpactedCPAStatistics.invWriteCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        invWriteTimer.start();

        if(ImpactedHelper.getInstance().isInvDisj) {
            for (Integer loc : locs) {
                if(!ImpactedHelper.getInstance().doAbstractionNodeNum.contains(loc))
                    continue;
                // System.out.println(loc.getNodeNumber());
                Triple<PredicatePrecision, PathFormula, Region> invariant = invariants.get(loc);
                PredicatePrecision prec = invariant.getFirst();
                PathFormula pathFormula = invariant.getSecond();
                Region region = invariant.getThird();
                BooleanFormula formula = absmgr.toConcrete(region);
                PredicateAbstractState pState = locToState.get(loc);
                AbstractionFormula oldAbsFormula = pState.getAbstractionFormula();
                //TODO qianshan may not be sound! because we do not preceed all of the items in AbstractionFormula
                AbstractionFormula absFormula = new AbstractionFormula(GlobalInfo.getInstance().getFormulaManagerView(),
                        region, formula, oldAbsFormula.asInstantiatedFormula(),
                        pathFormula, oldAbsFormula.getIdsOfStoredAbstractionReused());
                curVMemoryDisjInvariants.put(loc, Pair.of(prec, absFormula));
            }
        }

        try (FileOutputStream fileWriter = new FileOutputStream(invariantsFile.toFile());
             //ObjectOutputStream writerO = new ObjectOutputStream(fileWriter); //write object to file drectly

             ByteArrayOutputStream baostream = new ByteArrayOutputStream();
             ObjectOutputStream objOByte = new ObjectOutputStream(baostream); //write object to byte array

             ByteArrayOutputStream baostreamForZip = new ByteArrayOutputStream();
             GZIPOutputStream gzipToBytestream = new GZIPOutputStream(baostreamForZip); //compress byte array

             FilterOutputStream gzipO = ImpactedHelper.getInstance().parallelOutput ? new ParallelGZIPOutputStream(fileWriter) : new GZIPOutputStream(fileWriter);


             ObjectOutputStream objO = ImpactedHelper.getInstance().compressIO ? new ObjectOutputStream(gzipO) : new ObjectOutputStream(fileWriter)) {
            //just save newest precision
            Set<PrecisionHelpState> newestPrecisions = new PredicateAnalysisPrecisionExtractor().getNewestPrecision(reached);

             if(!ImpactedHelper.getInstance().isInvDisj) {
                for (Map.Entry<Pair<Integer, String>, AbstractState> curEntry : curVMemoryInvariants.entrySet()) {
                    if (!CPAMain.isReusePrecision || newestPrecisions.size() == 0 || newestPrecisions.contains(curEntry.getKey().getSecond())) {
                        //writer.write(FUNCTIONLINE + curEntry.getKey());//function name and precision
                        //Set<ARGState> subgraph = ((ARGState)curEntry.getValue()).getSubgraph();
                        Pair<String, String> loctofun = Pair.of("LOC: " + curEntry.getKey().getFirst(),
                                curEntry.getKey().getSecond());

                        if(!ImpactedHelper.jsonIO) {
                            // writerO.writeObject(loctofun);
                            // writerO.writeObject(curEntry.getValue());
                            // writerO.writeObject(null);

                            objOByte.writeObject(loctofun);
                            objOByte.writeObject(curEntry.getValue());
                            objOByte.writeObject(null);
                        }

                    }
                }
            } else {
                for(Map.Entry<Integer, Pair<PredicatePrecision, AbstractionFormula>> curEntry :
                        curVMemoryDisjInvariants.entrySet()) {
                    String locStr = "" + curEntry.getKey().toString();
                    //PrecisionHelpState curPHState =
                    //        new PrecisionHelpState(funName, reached.getPrecision(state), new PredicateAnalysisPrecisionExtractor());
                    if(!ImpactedHelper.jsonIO) {
                        try {

                            serializeCount += 1;
                            objO.writeObject(locStr);
                            //TODO qianshan CFANode cannot be serialized
                            //writerO.writeObject(GlobalInfo.getInstance().getCFAInfo().get().getNodeByNodeNumber(curEntry.getKey()));
                            //writerO.writeObject(curEntry.getValue().getFirst());
                            //writerO.writeObject(curEntry.getValue().getSecond());
                            //Pair<PredicatePrecision, AbstractionFormula> pair = curEntry.getValue();

                            checkArgument(curEntry.getValue() != null);

                            objO.writeObject(curEntry.getValue().getFirst());
                            objO.writeObject(curEntry.getValue().getSecond());
                            //writerO.writeObject(null);

                            //Pair<PredicatePrecision, AbstractionFormula> pair = curEntry.getValue();
                            //writerO.writeObject(pair.getFirst());
                            //writerO.writeObject(pair.getSecond().asFormula());
                            //writerO.writeObject(pair.getSecond().asInstantiatedFormula());
                            //objO.writeObject(null);
                        } catch (IOException e) {
                            System.out.println("serialization error");
                        }
                    } else {
                        // byte[] loctofun_bytes = ProtostuffIOUtil.toByteArray(loctofun, pair_schema, LinkedBuffer.allocate(LinkedBuffer.DEFAULT_BUFFER_SIZE));


                        AbstractionFormula absF = curEntry.getValue().getSecond();
                        //absF.clearForSer();

                        //byte[] loctofun_bytes = ProtostuffUtil.serializer(locStr);
                        //byte[] prec_bytes = ProtostuffUtil.serializer(curEntry.getValue().getFirst());

                        //int bfLen = absF.getBlockFormula().getLength();
                        //PointerTargetSet bfPTS = absF.getBlockFormula().getPointerTargetSet();

                        FormulaManagerView mgr = GlobalInfo.getInstance().getFormulaManagerView();
                        //String bfFormula = mgr.dumpFormula(absF.getBlockFormula().getFormula()).toString();
                        String formula = mgr.dumpFormula(absF.asFormula()).toString();
                        String instantiatedFormula = mgr.dumpFormula(absF.asInstantiatedFormula()).toString();

                        //byte[] bfLen_bytes = Integer.toString(bfLen).getBytes();
                        ////byte[] bfPTS_bytes = ProtostuffUtil.serializer(bfPTS);
                        //byte[] bfFormula_bytes = ProtostuffUtil.serializer(bfFormula);

                        //byte[] formula_bytes = ProtostuffUtil.serializer(formula);
                        //byte[] instantiatedFormula_bytes = ProtostuffUtil.serializer(instantiatedFormula);

                        //byte[] formula_bytes = ProtostuffUtil.serializer(locStr + '\n' + formula + '\n' + instantiatedFormula + '\n');
                        //output_stuff.concat(locStr + '\n' + formula + '\n' + instantiatedFormula + '\n');
                        //String prec_Str = new java.lang.String(prec_bytes);
                        //String tmp = locStr + "\n" + formula + "\n" + instantiatedFormula + "\n";
                        Pair<String, String> absFStr = Pair.of(formula, instantiatedFormula);
                        //byte[] absFStr_bytes = ProtostuffUtil.serializer(absFStr);
                        //Pair<byte[], Pair<String, String>> pair = Pair.of(prec_bytes, absFStr);
                        //Pair<PredicatePrecision, Pair<String, String>> pair = Pair.of(curEntry.getValue().getFirst(), absFStr);
                        objO.writeObject(locStr);
                        //objO.writeObject(pair);
                        objO.writeObject(absFStr);
                        objO.writeObject(null);

                        //System.out.println(curEntry.getValue().getFirst());
                        //output_stuff.append(tmp);
                        //byte[] instantiatedFormula_bytes = ProtostuffUtil.serializer(instantiatedFormula);


                        //System.out.println(loctofun_bytes);

                        //Gson gson = new GsonBuilder().excludeFieldsWithoutExposeAnnotation().create();
                        //Gson normal_gson = new Gson();
                        //String locStrfunJson = normal_gson.toJson(locStr);
                        //String precfunJson = normal_gson.toJson(curEntry.getValue().getFirst());
                        //String formulafunJson = gson.toJson(curEntry.getValue().getSecond());
                        //byte[] formula_bytes = formulafunJson.getBytes();
                        //String formulaJson = normal_gson.toJson(formula);
                        //String instantiatedFormulaJson = normal_gson.toJson(instantiatedFormula);

                        //fileWriter.write(locStr.getBytes());
                        //fileWriter.write("\n".getBytes());

                        //fileWriter.write(prec_bytes);
                        //fileWriter.write("\n".getBytes());

                        //fileWriter.write(formula_bytes);
                        //writerO.writeObject(absF);

                        //fileWriter.write(bfLen_bytes);
                        //fileWriter.write("\n".getBytes());

                        //fileWriter.write(bfPTS_bytes); //19MB/40MB
                        //fileWriter.write("\n".getBytes());

                        //fileWriter.write(bfFormula_bytes);
                        //fileWriter.write("\n".getBytes());

                        //fileWriter.write(formula_bytes);
                        //fileWriter.write(formula.getBytes());
                        //fileWriter.write("\n".getBytes());

                        //fileWriter.write(instantiatedFormula_bytes);
                        //fileWriter.write("\n".getBytes());

                        //fileWriter.write("\n".getBytes());
                    }
                }
                //byte[] formula_bytes = ProtostuffUtil.serializer(output_stuff.toString());
                //output_stuff.append("\n");
                //objO.writeObject(output_stuff.toString());
                if(ImpactedHelper.jsonIO) {
                    objO.writeObject(null);
                    //objO.close();
                    //gzipO.close();
                    //fileWriter.close();
                } else {
                    //byte[] rawData = baostream.toByteArray();
                    //gzipToBytestream.write(rawData);
                    //byte[] compressedData = baostreamForZip.toByteArray();
                    //fileWriter.write(compressedData);

                    //objO.write(compressedData);
                    objO.writeObject(null);
                }
                //fileWriter.write(output_stuff.toString().getBytes());
            }

            //writerO.writeObject(null);
            //writerO.flush();
            //fileWriter.flush();
            objO.close();

            gzipO.close();

            //gzipToBytestream.close();
            //baostreamForZip.close();

            //objOByte.close();
            //baostream.close();

            fileWriter.close();
            //gzipO.close();
        } catch (Exception e) {
            // TODO Auto-generated catch block
            System.out.println("serialization error");
            //e.printStackTrace();
        }

        // -- then the assertions
//            for (Map.Entry<ARGState, String> entry : stateToAssert.entrySet()) {
//                ARGState state = entry.getKey();
//                StringBuilder stateSuccessorsSb = new StringBuilder();
//                for (ARGState successor : successors.get(state)) {
//                    if (stateSuccessorsSb.length() > 0) {
//                        stateSuccessorsSb.append(",");
//                    }
//                    stateSuccessorsSb.append(getAbstractionId(successor));
//                }
//
//                writer.append(String.format("%d (%s) @%d:",
//                        getAbstractionId(state),
//                        stateSuccessorsSb.toString(),
//                        AbstractStates.extractLocation(state).getNodeNumber()));
//                writer.append("\n");
//                writer.append(entry.getValue());
//                writer.append("\n\n");
//            }

        stopCpuTime = 0;
        try {
            stopCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        invWriteTimer.stop();
        ImpactedCPAStatistics.invWriteCpuTime = stopCpuTime - ImpactedCPAStatistics.invWriteCpuTime;
    }

    void writeInvariantsPerFile(ReachedSet reached) {
        invCollectTimer.start();
        // in this set, we collect the string representing each predicate
        // (potentially making use of the above definitions)
        //Map<ARGState, String> stateToAssert = Maps.newHashMap();
        Map<Integer, PredicateAbstractState> locToState = Maps.newHashMap();

        // Get list of all abstraction states in the set reached
        ARGState rootState =
            AbstractStates.extractStateByType(reached.getFirstState(), ARGState.class);
        //SetMultimap<ARGState, ARGState> successors = ARGUtils.projectARG(rootState, ARGUtils.CHILDREN_OF_STATE, IS_ABSTRACTION_STATE);

        Set<ARGState> done = Sets.newHashSet();
        Deque<ARGState> worklist = Queues.newArrayDeque();

        worklist.add(rootState);

        ArrayList<Integer> locs = new ArrayList<>();
        Map<Integer, Triple<PredicatePrecision, PathFormula, Region>> invariants =
            Maps.newHashMap();


        while (!worklist.isEmpty()) {
            ARGState state = worklist.pop();
//                if(state.isCovered()) {
//                    continue;
//                }
            CompositeState comp = (CompositeState) state.getWrappedState();
            List<AbstractState> comps = comp.getWrappedStates();
            String funName = null;
            PredicateAbstractState pState = null;
            Integer locNum = -1;
            Integer loc = (extractLocation(state)).getNodeNumber();
            for (AbstractState s : comps) {
                if (s instanceof CallstackState) {
                    funName = ((CallstackState) s).getCurrentFunction();
                }
                if (s instanceof PredicateAbstractState) {
                    pState = (PredicateAbstractState) s;
                }
                if (s instanceof LocationState) {
                    locNum = ((LocationState) s).getLocationNode().getNodeNumber();
                }
            }


            if (done.contains(state)) {
                continue;
            }
            //children = (List<ARGState>) state.getChildren();
            // Handle successors
            worklist.addAll(state.getChildren());

            // Abstraction formula
            //BooleanFormula formula = pState.getAbstractionFormula().asFormula();

            //Pair<String, List<String>> p = splitFormula(fmgr, formula);
            //String formulaString = p.getFirst();


            //stateToAssert.put(state, formulaString);
            if (!state.isCovered() && !ImpactedHelper.getInstance().isInvDisj) {
                //Precisions.extractPrecisionByType(reached.getPrecision(state), PredicatePrecision.class);
                PrecisionHelpState curPHState =
                    new PrecisionHelpState(funName, reached.getPrecision(state),
                        new PredicateAnalysisPrecisionExtractor());
                curVMemoryInvariants.put(Pair.of(locNum, curPHState.toString()), pState);
            } else if (!state.isCovered() && ImpactedHelper.getInstance().isInvDisj) {
                //PredicatePrecision prec = Precisions.extractPrecisionByType(reached.getPrecision(state), PredicatePrecision.class);
                Triple<PredicatePrecision, PathFormula, Region> invariant = invariants.get(loc);
                PredicatePrecision prec = null;
                PathFormula pathFormula = null;
                Region region = null;
                if (invariant != null) {
                    prec = invariant.getFirst();
                    pathFormula = invariant.getSecond();
                    region = invariant.getThird();
                }

                PathFormula curPathFormula = pState.getPathFormula();

                try {
                    if (pathFormula == null) {
                        pathFormula = curPathFormula;
                    } else {
                        invCollectMergeTimer.start();
                        invCollectPathFormulaTimer.start();
                        if (ImpactedHelper.getInstance().aggressive_pathformula) {
                            pathFormula = GlobalInfo.getInstance().getPathFormulaManager()
                                .makeOrLight(pathFormula, curPathFormula);
                        } else {
                            pathFormula = GlobalInfo.getInstance().getEmptyPathFormula();
                        }
                        invCollectPathFormulaTimer.stop();
                        invCollectMergeTimer.stop();
                    }
                } catch (InterruptedException e) {
                    e.printStackTrace();
                }

                region = firstNonNull(region, rmgr.makeFalse());
                PredicatePrecision curPrec = Precisions
                    .extractPrecisionByType(reached.getPrecision(state), PredicatePrecision.class);
                Region curRegion = pState.getAbstractionFormula().asRegion();
                if (prec == null) {
                    prec = curPrec;
                } else {
                    invCollectMergeTimer.start();
                    invCollectPrecTimer.start();
                    prec = prec.mergeWith(curPrec);
                    invCollectPrecTimer.stop();
                    invCollectMergeTimer.stop();
                }

                invCollectMergeTimer.start();
                invCollectRegionTimer.start();
                region = rmgr.makeOr(region, curRegion);
                invCollectRegionTimer.stop();
                invCollectMergeTimer.stop();

                if (!locs.contains(loc))
                    locs.add(loc);
                invariants.put(loc, Triple.of(prec, pathFormula, region));
                locToState.put(loc, pState);
            }
            done.add(state);
        }

        invCollectTimer.stop();

        try {
            ImpactedCPAStatistics.invWriteCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        invWriteTimer.start();

        if (ImpactedHelper.getInstance().isInvDisj) {
            for (Integer loc : locs) {
                if (!ImpactedHelper.getInstance().doAbstractionNodeNum.contains(loc))
                    continue;
                // System.out.println(loc.getNodeNumber());
                Triple<PredicatePrecision, PathFormula, Region> invariant = invariants.get(loc);
                PredicatePrecision prec = invariant.getFirst();
                PathFormula pathFormula = invariant.getSecond();
                Region region = invariant.getThird();
                BooleanFormula formula = absmgr.toConcrete(region);
                PredicateAbstractState pState = locToState.get(loc);
                AbstractionFormula oldAbsFormula = pState.getAbstractionFormula();
                //TODO qianshan may not be sound! because we do not preceed all of the items in AbstractionFormula
                AbstractionFormula absFormula =
                    new AbstractionFormula(GlobalInfo.getInstance().getFormulaManagerView(),
                        region, formula, oldAbsFormula.asInstantiatedFormula(),
                        pathFormula, oldAbsFormula.getIdsOfStoredAbstractionReused());
                curVMemoryDisjInvariants.put(loc, Pair.of(prec, absFormula));
            }
        }


        for (Map.Entry<Integer, Pair<PredicatePrecision, AbstractionFormula>> curEntry :
            curVMemoryDisjInvariants.entrySet()) {
            String locStr = "" + curEntry.getKey().toString();
            //PrecisionHelpState curPHState =
            //        new PrecisionHelpState(funName, reached.getPrecision(state), new PredicateAnalysisPrecisionExtractor());
            try {

                serializeCount += 1;
                Path invariantPerFile = Paths.get("tmp","invariants_" + locStr + ".txt");
                FileOutputStream fileWriter = new FileOutputStream(invariantPerFile.toFile());
                ObjectOutputStream objO = new ObjectOutputStream(fileWriter);
                objO.writeObject(locStr);
                //TODO qianshan CFANode cannot be serialized
                //writerO.writeObject(GlobalInfo.getInstance().getCFAInfo().get().getNodeByNodeNumber(curEntry.getKey()));
                //writerO.writeObject(curEntry.getValue().getFirst());
                //writerO.writeObject(curEntry.getValue().getSecond());
                //Pair<PredicatePrecision, AbstractionFormula> pair = curEntry.getValue();

                checkArgument(curEntry.getValue() != null);

                objO.writeObject(curEntry.getValue().getFirst());
                objO.writeObject(curEntry.getValue().getSecond());
                //writerO.writeObject(null);

                //Pair<PredicatePrecision, AbstractionFormula> pair = curEntry.getValue();
                //writerO.writeObject(pair.getFirst());
                //writerO.writeObject(pair.getSecond().asFormula());
                //writerO.writeObject(pair.getSecond().asInstantiatedFormula());
                //objO.writeObject(null);
                objO.close();
                fileWriter.close();
            } catch (IOException e) {
                System.out.println("serialization error");
            }
        }

    }
}
