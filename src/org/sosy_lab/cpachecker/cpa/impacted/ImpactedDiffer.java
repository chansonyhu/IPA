package org.sosy_lab.cpachecker.cpa.impacted;

import com.google.common.collect.ImmutableList;
import java.util.logging.Level;
import org.python.core.PyObject;
import org.python.core.PyString;
import org.python.util.PythonInterpreter;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.common.io.Files;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.Paths;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.CFACreator;
import org.sosy_lab.cpachecker.cfa.export.DOTBuilder;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cmdline.CPAMain;

import java.io.*;
import java.nio.charset.Charset;
import java.util.ArrayList;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;

import static com.google.common.base.Preconditions.checkArgument;

@Options(prefix="cpa.impacted")
public class ImpactedDiffer {
    private static ImpactedDiffer instance;

    @Option(secure=true, name="currentCfa.file",
        description="export CFA as .dot file")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    private Path currentCfaFile = Paths.get("current_cfa.dot");

    @Option(secure=true, name="previousCfa.file",
        description="export CFA as .dot file")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    private Path previousCfaFile = Paths.get("previous_cfa.dot");

    @Option(secure=true, description="file for diff",
            name="diff.file")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    private Path diffFile = Paths.get("diff.txt");

    @Option(secure=true, name="old.file", description="old program file")
    @FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
    private Path oldProgram = null;

    @Option(secure=true, name="diff.cfaInfo", description="cfadiff file path")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    public Path cfaInfoPath;

    private Path absOldProgram = null;
    //@Option(secure=true, name="analysis.programNames", description="new program file")
    //@FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
    //private Path newProgram = Paths.get("~/Exp/cpachecker-summary/exp/lazyExpansion/ldv-benchmark/xen--xenfs--xenfs.c_1/xen--xenfs--xenfs.c");
    private String absNewProgram;


    private final String cfaInfoPrefix;

    private boolean isInputValid = true;

    private ImpactedDiffer(Configuration pConfig) {
        absNewProgram = CPAMain.program;
        String[] tmp;
        String file_name;
        if(GlobalInfo.getInstance().cfaInfoPath != null) {
            tmp = GlobalInfo.getInstance().cfaInfoPath.split("/");
            file_name = tmp[tmp.length - 1];
            cfaInfoPrefix = file_name.split("\\.")[0];
        } else {
            cfaInfoPrefix = null;
        }
        try {
            pConfig.inject(this, ImpactedDiffer.class);
        } catch (InvalidConfigurationException e) {
            isInputValid = false;
        }
        GlobalInfo.getInstance().cfaInfoPrefix = cfaInfoPrefix;
    }

    private void diffGenerate(String diffPath) throws IOException {

        ArrayList<String> codeLines = new ArrayList<>();
        BufferedReader reader = new BufferedReader(new InputStreamReader(new FileInputStream(absOldProgram.toFile()), Charset.defaultCharset()));

        for (String rawline = reader.readLine(); rawline != null; rawline = reader.readLine())
        {
            codeLines.add(rawline);
        }
        reader.close();

        int[] lineBias = new int[codeLines.size()];

        int i = 0;
        //BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(mixPath), Charset.defaultCharset()));

        reader = new BufferedReader(new InputStreamReader(new FileInputStream(diffPath), Charset.defaultCharset()));
        boolean align = true;
        for (String rawline = reader.readLine(); rawline != null; rawline = reader.readLine()) {
            char operation = rawline.charAt(0);
            if(operation != 'd' && operation != 'a') {
                if(!(reader.readLine() == null))
                    System.out.println("diff file invalid!");
                break;
            }
            String impactNote = "/*@ impact pragma stmt; */";
            String[] nums = rawline.substring(1).split("\\s");
            int lineNum = Integer.valueOf(nums[0]);
            int operationNum = Integer.valueOf(nums[1]);

            if (operation == 'd') {
                align = false;
            }
            //else
            if (operation == 'a') {
                for (int j = 0; j < operationNum; ++j) {
                    ImpactedHelper.getInstance().impactedLines.add(Integer.valueOf((rawline.split(" ")[0]).split("a")[1]));
                }
                assert !align;
                align = true;
            }
        }
        checkArgument(align);
        reader.close();
    }

    public void diff() throws IOException, InterruptedException {
        if(oldProgram == null)
            return;
        String rawline;
        //String mixPath = "newversion/sourcecode/CPAChecker/Impacted/diff.c";
        //String impactPath = "impact.txt";
        String diffPath = diffFile.getAbsolutePath();
        absNewProgram = CPAMain.program;
        //absOldProgram = Paths.get(progBase.toFile().toString(), oldProgram.toFile().toString());
        absOldProgram = Paths.get(oldProgram.toFile().toString());
        String command = "diff -b -B -H -n " + absOldProgram.toString() + " " + absNewProgram.toString();
        BufferedReader reader;
        BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(diffPath), Charset.defaultCharset()));
        Process p = Runtime.getRuntime().exec(command);

        p.waitFor();
        reader = new BufferedReader(new InputStreamReader(p.getInputStream(), Charset.defaultCharset()));
        rawline = reader.readLine();
        if (rawline != null)
        {
            writer.write(rawline);
            for (rawline = reader.readLine(); rawline != null; rawline = reader.readLine())
            {
                writer.newLine();
                writer.write(rawline);
            }
        }
        reader.close();
        writer.close();
        p.destroy();

        diffGenerate(diffPath);

    }

    public void cfadiff(CFA previousCfa, CFA currentCfa, LogManager logger) throws IOException{

        try (Writer w = Files.openOutputFile(currentCfaFile)) {
            DOTBuilder.generateDOT(w, currentCfa);
        } catch (IOException e) {
            logger.logUserException(Level.WARNING, e,
                "Could not write CFA to dot file");
            // continue with analysis
        }

        try (Writer w = Files.openOutputFile(previousCfaFile)) {
            DOTBuilder.generateDOT(w, previousCfa);
        } catch (IOException e) {
            logger.logUserException(Level.WARNING, e,
                "Could not write CFA to dot file");
            // continue with analysis
        }
        try {
            String[] args0 = new String[] { "python", "./sf-cfadiff/cfadiff.pyc",
                "--old",
                String.valueOf(currentCfaFile).replace("\\","/"), "--new", String.valueOf(
                previousCfaFile).replace("\\","/"), "--fuzz"
                , "0", "--eps", "0.5"};
            Process proc = Runtime.getRuntime().exec(args0);// 执行py文件
            BufferedReader in = new BufferedReader(new InputStreamReader(proc.getInputStream()));
            String rawline;
            rawline = in.readLine();
            if(rawline != null) {
                while(!(rawline = in.readLine()).equals("Mapping end.")) {
                    if(rawline.equals("Mapping begin."))
                        continue;
                    if(rawline.contains("oldID") || rawline.contains("None")) continue;
                    String[] rawIDs = (rawline.split("#")[0]).trim().split(",");
                    checkArgument(rawIDs.length >= 1);
                    if(rawIDs[0].contains("node"))
                        continue;
                    int newID = Integer.parseInt(rawIDs[0].trim());
                    int oldID = -1;
                    if(rawIDs.length == 2) oldID = Integer.parseInt(rawIDs[1].trim());
                    ImpactedHelper.getInstance().cfa_newID2oldID.put(newID, oldID);
                    ImpactedHelper.getInstance().cfa_oldID2newID.put(oldID, newID);
                }

                while(!(rawline = in.readLine()).equals("Added end.")) {
                    if(rawline.equals("Added begin."))
                        continue;
                    if(rawline.contains("oldID")) continue;
                    String[] rawIDs = (rawline.split("#")[0]).trim().split(",");
                    String[] tmpFrags = rawline.split("\"");
                    String rawStmt = "";
                    if(tmpFrags.length > 1) {
                        rawStmt = tmpFrags[1].trim();
                    }
                    checkArgument(rawIDs.length == 2);
                    //checkArgument(!rawStmt.equals(""));
                    int pred = Integer.parseInt(rawIDs[0].trim());
                    int succ = Integer.parseInt(rawIDs[1].trim());
                    SimpleEdge edge = new SimpleEdge(pred, succ, rawStmt, decideEdgeType(rawStmt));
                    ImpactedHelper.getInstance().cfa_deleted_edges.put(Pair.of(pred, succ), edge);
                }

                while(!(rawline = in.readLine()).equals("Deleted end.")) {
                    if(rawline.equals("Deleted begin."))
                        continue;
                    if(rawline.contains("newID")) continue;
                    String[] rawIDs = (rawline.split("#")[0]).trim().split(",");
                    String[] tmpFrags = rawline.split("\"");
                    String rawStmt = "";
                    if(tmpFrags.length > 1) {
                        rawStmt = tmpFrags[1].trim();
                    }
                    checkArgument(rawIDs.length == 2);
                    //checkArgument(!rawStmt.equals(""));
                    int pred = Integer.parseInt(rawIDs[0].trim());
                    int succ = Integer.parseInt(rawIDs[1].trim());
                    SimpleEdge edge = new SimpleEdge(pred, succ, rawStmt, decideEdgeType(rawStmt));
                    ImpactedHelper.getInstance().cfa_added_edges.put(Pair.of(pred, succ), edge);
                }

                while(!(rawline = in.readLine()).equals("Modified end.")) {
                    if(rawline.equals("Modified begin."))
                        continue;
                    String line = rawline;
                    ArrayList<String> lines = new ArrayList();
                    if(line.startsWith("False") || line.startsWith("True")) {
                        continue;
                    }
                    lines.add(line);
                    line = in.readLine();
                    lines.add(line);
                    line = in.readLine();
                    lines.add(line);
                    line = in.readLine();
                    lines.add(line);

                    checkArgument(lines.size() == 4);
                    String[] rawNewIDs = lines.get(0).split("#")[0].trim().split(",");
                    String[] rawOldIDs = lines.get(1).split("#")[0].trim().split(",");
                    String[] tmpFrags = lines.get(2).split("\"");
                    String rawNewStmt = "";
                    String rawOldStmt = "";
                    if(tmpFrags.length > 2) {
                        rawNewStmt = tmpFrags[1].trim();
                    }
                    tmpFrags = lines.get(3).split("\"");
                    if(tmpFrags.length > 2) {
                        rawOldStmt = tmpFrags[1].trim();
                    }

                    checkArgument(rawOldIDs.length == 2);
                    checkArgument(rawNewIDs.length == 2);

                    int oldPred = Integer.parseInt(rawOldIDs[0].trim());
                    int oldSucc = Integer.parseInt(rawOldIDs[1].trim());
                    int newPred = Integer.parseInt(rawNewIDs[0].trim());
                    int newSucc = Integer.parseInt(rawNewIDs[1].trim());

                    SimpleEdge oldEdge = new SimpleEdge(oldPred, oldSucc, rawOldStmt, decideEdgeType(rawOldStmt));
                    SimpleEdge newEdge = new SimpleEdge(newPred, newSucc, rawNewStmt, decideEdgeType(rawNewStmt));
                    ImpactedHelper.getInstance().cfa_modified_edges.put(Pair.of(newPred, newSucc), Pair.of(oldEdge, newEdge));
                }
            }
            in.close();
            proc.waitFor();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
//        System.out.println("Number of added edges: " + ImpactedHelper.getInstance().cfa_added_edges.size());
//        System.out.println("Number of deleted edges: " + ImpactedHelper.getInstance().cfa_deleted_edges.size());
        System.out.println("Number of modified edges: " + ImpactedHelper.getInstance().cfa_modified_edges.size());
    }

    public void cfadiff_external() throws IOException{
        if(ImpactedHelper.getInstance().cfaInfoPath == null)
            return;
        if(ImpactedHelper.getInstance().isCfaSame)
            return;
        final String EDGE_ADD = cfaInfoPrefix + ".edge.add";
        final String EDGE_DEL = cfaInfoPrefix + ".edge.del";
        final String EDGE_MOD = cfaInfoPrefix + ".edge.mod";
        final String NODE_MATCH = cfaInfoPrefix + ".ptmatch";
        if(cfaInfoPath == null) {
            cfaInfoPath = ImpactedHelper.getInstance().cfaInfoPath;
            //System.out.println("empty cfa diff path!");
        }

        Path edge_add_file = Paths.get(cfaInfoPath.toString(), EDGE_ADD);
        Path edge_del_file = Paths.get(cfaInfoPath.toString(), EDGE_DEL);
        Path edge_mod_file = Paths.get(cfaInfoPath.toString(), EDGE_MOD);
        Path node_match_file = Paths.get(cfaInfoPath.toString(), NODE_MATCH);
        BufferedReader reader;

        if(!node_match_file.exists()) throw new FileNotFoundException();
        reader = new BufferedReader(new InputStreamReader(new FileInputStream(node_match_file.getAbsolutePath()), Charset.defaultCharset()));

        for (String rawline = reader.readLine(); rawline != null; rawline = reader.readLine()) {
            if(rawline.contains("oldID") || rawline.contains("None")) continue;
            String[] rawIDs = (rawline.split("#")[0]).trim().split(",");
            checkArgument(rawIDs.length == 2);
            if(rawIDs[0].contains("node"))
                continue;
            int oldID = Integer.valueOf(rawIDs[0].trim());
            int newID = Integer.valueOf(rawIDs[1].trim());
            ImpactedHelper.getInstance().cfa_newID2oldID.put(newID, oldID);
            ImpactedHelper.getInstance().cfa_oldID2newID.put(oldID, newID);
        }

        reader = new BufferedReader(new InputStreamReader(new FileInputStream(edge_add_file.getAbsolutePath()), Charset.defaultCharset()));

        for (String rawline = reader.readLine(); rawline != null; rawline = reader.readLine()) {
            if(rawline.contains("newID")) continue;
            String[] rawIDs = (rawline.split("#")[0]).trim().split(",");
            String[] tmpFrags = rawline.split("\"");
            String rawStmt = "";
            if(tmpFrags.length > 1) {
                rawStmt = tmpFrags[1].trim();
            }
            checkArgument(rawIDs.length == 2);
            //checkArgument(!rawStmt.equals(""));
            int pred = Integer.valueOf(rawIDs[0].trim());
            int succ = Integer.valueOf(rawIDs[1].trim());
            SimpleEdge edge = new SimpleEdge(pred, succ, rawStmt, decideEdgeType(rawStmt));
            ImpactedHelper.getInstance().cfa_added_edges.put(Pair.of(pred, succ), edge);
        }

        reader = new BufferedReader(new InputStreamReader(new FileInputStream(edge_del_file.getAbsolutePath()), Charset.defaultCharset()));

        for (String rawline = reader.readLine(); rawline != null; rawline = reader.readLine()) {
            if(rawline.contains("oldID")) continue;
            String[] rawIDs = (rawline.split("#")[0]).trim().split(",");
            String[] tmpFrags = rawline.split("\"");
            String rawStmt = "";
            if(tmpFrags.length > 1) {
                rawStmt = tmpFrags[1].trim();
            }
            checkArgument(rawIDs.length == 2);
            //checkArgument(!rawStmt.equals(""));
            int pred = Integer.valueOf(rawIDs[0].trim());
            int succ = Integer.valueOf(rawIDs[1].trim());
            SimpleEdge edge = new SimpleEdge(pred, succ, rawStmt, decideEdgeType(rawStmt));
            ImpactedHelper.getInstance().cfa_deleted_edges.put(Pair.of(pred, succ), edge);
        }

        reader = new BufferedReader(new InputStreamReader(new FileInputStream(edge_mod_file.getAbsolutePath()), Charset.defaultCharset()));

        for (String rawline = reader.readLine(); rawline != null; rawline = reader.readLine()) {
            String line = rawline;
            ArrayList<String> lines = new ArrayList();
//            while(!line.startsWith("False") && !line.startsWith("True")) {
//                lines.add(line);
//                line = reader.readLine();
//            }
            if(line.startsWith("False") || line.startsWith("True")) {
                continue;
            }
            lines.add(line);
            line = reader.readLine();
            lines.add(line);
            line = reader.readLine();
            lines.add(line);
            line = reader.readLine();
            lines.add(line);

            checkArgument(lines.size() == 4);
            String[] rawOldIDs = lines.get(0).split("#")[0].trim().split(",");
            String[] rawNewIDs = lines.get(1).split("#")[0].trim().split(",");
            String[] tmpFrags = lines.get(2).split("\"");
            String rawOldStmt = "";
            String rawNewStmt = "";
            if(tmpFrags.length > 2) {
                rawOldStmt = tmpFrags[1].trim();
            }
            tmpFrags = lines.get(3).split("\"");
            if(tmpFrags.length > 2) {
                rawNewStmt = tmpFrags[1].trim();
            }

            checkArgument(rawOldIDs.length == 2);
            checkArgument(rawNewIDs.length == 2);

            int oldPred = Integer.valueOf(rawOldIDs[0].trim());
            int oldSucc = Integer.valueOf(rawOldIDs[1].trim());
            int newPred = Integer.valueOf(rawNewIDs[0].trim());
            int newSucc = Integer.valueOf(rawNewIDs[1].trim());

            SimpleEdge oldEdge = new SimpleEdge(oldPred, oldSucc, rawOldStmt, decideEdgeType(rawOldStmt));
            SimpleEdge newEdge = new SimpleEdge(newPred, newSucc, rawNewStmt, decideEdgeType(rawNewStmt));
            ImpactedHelper.getInstance().cfa_modified_edges.put(Pair.of(newPred, newSucc), Pair.of(oldEdge, newEdge));
        }

        reader.close();
    }

    public static ImpactedDiffer getInstance() {
        if(instance == null) {
            instance = new ImpactedDiffer(CPAMain.cpaConfig);
        }
        return instance;
    }

    private CFAEdgeType decideEdgeType(String rawStmt) {
        return CFAEdgeType.UnknownEdge;
    }
}
