package org.sosy_lab.cpachecker.cpa.impacted;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.zip.GZIPInputStream;
import javax.management.JMException;
import org.matheclipse.core.reflection.system.Im;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;

import java.io.*;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.resources.ProcessCpuTime;

public class InvariantsReader {
    static private final AbstractionManager absmgr =
        GlobalInfo.getInstance().getAbstractionManager();
    public final static Timer invReadTimer = new Timer();

    static void loadInvariantFromFileSimple(File file) throws IOException{

        invReadTimer.start();
        try {
            ImpactedCPAStatistics.invReadCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        if (!file.exists()) {
            System.out.println("Invariant file not found!");
            ImpactedCPAStatistics.invReadCpuTime = 0;
            invReadTimer.stop();
            return;
        }
        GlobalInfo.getInstance().invariant_fs = file.length();
        try (FileInputStream fileReader = new FileInputStream(file);

             GZIPInputStream gzipR = new GZIPInputStream(fileReader);
             ObjectInputStream objR = ImpactedHelper.getInstance().compressIO ? new ObjectInputStream(gzipR) : new ObjectInputStream(fileReader)) {

            String key = (String) objR.readObject();
            while (!ImpactedHelper.jsonIO && key != null) {
                Integer loc;

                loc = Integer.valueOf(key);

                Object absFormula = objR.readObject();
                if(absFormula instanceof String) {
                    loc = Integer.valueOf((String) absFormula, 10);
                    absFormula = objR.readObject();
                }

                if(absFormula != null)
                    checkArgument(absFormula instanceof AbstractionFormula);
                if(absFormula == null)
                    continue;
                checkArgument(absFormula instanceof AbstractionFormula);
                Pair<PredicatePrecision, AbstractionFormula> disjInv =
                    Pair.of(new PredicatePrecision(), (AbstractionFormula) absFormula);
                if(ImpactedHelper.getInstance().externalDiff) {
                    Integer newID =  ImpactedHelper.getInstance().cfa_oldID2newID.get(loc);
                    if(newID == null && !ImpactedHelper.getInstance().cfa_oldID2newID.isEmpty() && !ImpactedHelper.getInstance().isOmitMatching) {
                        key = (String) objR.readObject();
                        if(key == null) {
                            System.out.println("Read invariant objects done");
                            break;
                        }
                        try {
                            Integer.valueOf(key);
                        } catch (NumberFormatException nfe) {
                            nfe.printStackTrace();
                            System.exit(1);
                        }
                        continue;
                    }
                    if((ImpactedHelper.getInstance().isOmitMatching && newID == null) || (newID == null && ImpactedHelper.getInstance().cfa_oldID2newID.isEmpty())) {
                        if(!ImpactedHelper.getInstance().isCfaSame) {
                            ImpactedHelper.getInstance().omits += 1;
                            //newID = loc;
                            newID = -1;
                        } else {
                            newID = loc;
                        }
                    }
                    ImpactedHelper.getInstance().lastVFileDisjInvariants.put(newID, disjInv);
                } else {
                    if(ImpactedHelper.getInstance().cfa_oldID2newID.containsKey(loc)) {
                        Integer newID = ImpactedHelper.getInstance().cfa_oldID2newID.get(loc);
                        ImpactedHelper.getInstance().lastVFileDisjInvariants.put(newID, disjInv);
                    }
//                    else if(ImpactedHelper.getInstance().cfa_modified_edges.size() == 0 && ImpactedHelper.getInstance().cfa_added_edges.size() == 0
//                    && ImpactedHelper.getInstance().cfa_deleted_edges.size() == 0) {
//                        ImpactedHelper.getInstance().lastVFileDisjInvariants.put(loc, disjInv);
//                    }
                }
                key = (String) objR.readObject();
                if(key == null) {
                    System.out.println("Read invariant objects done");
                    break;
                }
                try {
                    Integer.valueOf(key);
                } catch (NumberFormatException nfe) {
                    System.out.println("Line 328");
                    nfe.printStackTrace();
                    System.exit(1);
                }
            }


        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            System.out.println("Cannot read the invariant file.");
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        }
        long stopCpuTime = 0;
        try {
            stopCpuTime = ProcessCpuTime.read();
        } catch (JMException pE) {
            pE.printStackTrace();
        }
        invReadTimer.stop();
        ImpactedCPAStatistics.invReadCpuTime = stopCpuTime - ImpactedCPAStatistics.invReadCpuTime;
    }

}
