package org.sosy_lab.cpachecker.cpa.impacted;

import ap.proof.goal.Goal;
import java.util.concurrent.TimeUnit;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.Paths;
import org.sosy_lab.common.time.TimeSpan;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.CPAcheckerResult;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.modifications.ModificationsCPA;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecisionAdjustment;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.RegionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.statistics.AbstractStatistics;

import java.io.PrintStream;
import org.sosy_lab.common.time.Timer;

@Options(prefix="cpa.impacted")
public class ImpactedCPAStatistics extends AbstractStatistics {

    @Option(secure = true, description = "export final loop invariants",
            name = "invariants.export")
    private boolean exportInvariants = true;

    @Option(secure = true, description = "file for exporting final loop invariants",
            name = "invariants.file")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    private Path invariantsFile = Paths.get("impacted-invariants.txt");

    private String invariantsPath = null;

    private final ImpactedCPA cpa;
    private final AbstractionManager absmgr;
    private final RegionManager rgmr;
    private final InvariantsWriter invariantsWriter;
    static long invReadCpuTime;
    static long invWriteCpuTime;
    public static long invCollectCpuTime = 0;
    public static long invCheckCpuTimeInterval = 0;
    public static long invCheckCpuTime = 0;


    private Timer writeInvariantsTimer = new Timer();

    ImpactedCPAStatistics(ImpactedCPA pCpa, Configuration pConfig, AbstractionManager pAbsmgr, RegionManager pRmgr) {
        cpa = pCpa;
        absmgr = pAbsmgr;
        rgmr = pRmgr;
        try {
            pConfig.inject(this, ImpactedCPAStatistics.class);
        } catch (InvalidConfigurationException e) {
            e.printStackTrace();
        }
        final FormulaManagerView fmgr = cpa.getSolver().getFormulaManager();
        this.invariantsWriter = new InvariantsWriter(cpa.getLogger(), absmgr, fmgr, rgmr, cpa);
        if(exportInvariants && invariantsFile != null) {
            CPAMain.isReuseInvariant = true;
            String name = invariantsFile.getName();
            String path = invariantsFile.getPath().split(name)[0];
            CPAMain.invariantOutputPath = path;
        }
    }

    @Override
    public void printStatistics(PrintStream out, CPAcheckerResult.Result result, ReachedSet reached) {
        if (exportInvariants && invariantsFile != null) {
            writeInvariantsTimer.start();
            //if(result != Result.UNKNOWN) {
            invariantsWriter.writeInvariantsSimple(invariantsFile);
            //}
            writeInvariantsTimer.stop();
        }
        if(ImpactedHelper.getInstance().invariantsFile.toString().contains("null.txt")){
            return;
        }
        Integer invariantsSize = !ImpactedHelper.getInstance().isInvDisj ?
                                 ImpactedHelper.getInstance().lastVFileInvariants.size() : ImpactedHelper
                                     .getInstance().lastVFileDisjInvariants.size();
        if(ImpactedHelper.getInstance().isInvDisj) {
            out.println("  Number of invariants partial hits:                            " + ImpactedHelper.partialHits);
            out.println("  Number of invariants hits:                                    " + ImpactedHelper.hits);
            out.println("  Number of invariants trys:                                    " + ImpactedHelper.trys);
            out.println("  Number of invariants bots:                                    " + ImpactedHelper.bots);
            out.println("  Number of invariants not valid:                               " + ImpactedHelper.nonvalids);
//            out.println("  CFADiff matched nodes:                                        " + ModificationsCPA.match + " (" + ModificationsCPA.allnodes + ")");
//            String tmp = "no";
//            if(ModificationsCPA.misfit)
//                tmp = "yes";
//            out.println("  CFADiff misfit:                                               " + tmp);
        } else {
            out.println("  Number of invariants hits:                                    " + ImpactedHelper.hits + " (" + invariantsSize + ")");
        }
        out.println("  Initial reached size:                                         " + ImpactedHelper.getInstance().initialReachedSize);
        out.println("  Input invariants file size:                                   " + GlobalInfo.getInstance().invariant_fs);
        out.println("  Max impacted number of variables:                             " + ImpactedHelper.getInstance().maxImpactedNumWhenCPA);
        // out.println("  Max impacted number of variables (traverse):                  " +
        // ImpactedHelper.getInstance().maxImpactedNum);
//        int invSize = GlobalInfo.getInstance().lastInvSize == -1 ? ImpactedHelper.getInstance().lastVFileDisjInvariants.size() : GlobalInfo.getInstance().lastInvSize;
        out.println("  Number of last version invariants:                            " + ImpactedHelper.lastInvs);
        out.println("  Number of this version invariants:                            " + invariantsWriter.getOutputInvCount());
        // out.println("  Number of this version serialize invariants:                  " +
        // invariantsWriter.serializeCount);
        out.println("  CPU time for invariant read:                                  " + TimeSpan.ofNanos(invReadCpuTime).formatAs(TimeUnit.SECONDS));
        out.println("  CPU time for invariant write:                                 " + TimeSpan.ofNanos(invWriteCpuTime).formatAs(TimeUnit.SECONDS));
        // out.println("  CPU time for invariant collection:                            " +
        // TimeSpan.ofNanos(invCollectCpuTime).formatAs(TimeUnit.SECONDS));
        out.println("  Time for invariant write:                                     " + invariantsWriter.invWriteTimer);
        out.println("  Time for invariant read:                                      " + InvariantsReader.invReadTimer);
//        out.println("  Time for invariant collection:                                " + invariantsWriter.invCollectTimer);
//        out.println("    Time for invariant collection pathformula:                  " + invariantsWriter.invCollectPathFormulaTimer);
//        out.println("    Time for invariant collection prec:                         " + invariantsWriter.invCollectPrecTimer);
//        out.println("    Time for invariant collection region:                       " + invariantsWriter.invCollectRegionTimer);
//        out.println("  Time for invariant merge:                                     " + invariantsWriter.invCollectMergeTimer);
        //out.println("  Time for invariant write:                                     " + writeInvariantsTimer.toString());
        //out.println("  Total time for successor computation:                         " +
        // ImpactedTransferRelation.totalPostTime);
//        out.println("  Omits of node matching:                                       " + ImpactedHelper.getInstance().omits + " (" + GlobalInfo.getInstance().getCFAInfo().get().size() + ")");

    }

    public Path getInvariantFile() {
        return invariantsFile;
    }

    public String getInvariantsPath() {
        return invariantsPath;
    }

    public boolean isReuseInvariant() {
        return exportInvariants && invariantsFile != null;
    }
}