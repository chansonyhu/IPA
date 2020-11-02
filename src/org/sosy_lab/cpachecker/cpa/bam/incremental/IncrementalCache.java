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

import java.io.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;

import org.eclipse.cdt.utils.AR;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.time.TimeSpan;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cfa.blocks.Block;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.MainCPAStatistics;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.bam.BAMCache;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.ProgramInfo;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaManager;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.IOUtil;

public class IncrementalCache {

  private static IncrementalCache instance;

  //function name,precision-input output pairs, memory to file operation use this
  private Map<PrecisionHelpState, List<OneFileStore>> lastVFileCache = new HashMap<>();
  private Map<PrecisionHelpState, List<OneFileStore>> lastVFileCache_test = new HashMap<>();
  private Map<PrecisionHelpState, AbstractState> lastVFileSubgraph = new HashMap<>();

  //help to calculate if the cache is hit
  private Map<PrecisionHelpState, Map<EqualHelpState, OneFileStore>> lastVMemoryCache = new HashMap<>();
  private Map<PrecisionHelpState, AbstractState> lastVMemorySubgraph = new HashMap<>();
  private Map<PrecisionHelpState, Map<EqualHelpState, OneFileStore>> curVMemoryCache = new HashMap<>();
  private Map<PrecisionHelpState, AbstractState> curVMemorySubgraph = new HashMap<>();

  private int lastVCanUseSummarySize = 0;

  public int getLastVCanUseLoopSummarySize() {
    return lastVCanUseLoopSummarySize;
  }

  private int lastVCanUseLoopSummarySize = 0;
  private boolean isLoaded;
  private boolean canUseFileCache = true;
  private PrecisionExtractor precisionExtractor;
  private OutputStateBuilder outputStateBuilder;

  private Timer isCacheHitTimer = new Timer();
  private Timer readFileTimer = new Timer();
  private Timer writeFileTimer = new Timer();

  public static int funcHits = 0;
  public static int loopHits = 0;

  public static final String FUNCTIONLINE = "FUN:";
  public static final String FUNCTIONNAMEPRECISIONSPLIT = "\n";

  //qianshan. enable logger
  protected final LogManager logger = CPAMain.logManager;

  private IncrementalCache() {
    switch (CPAMain.abstractType) {
    case VALUEANALYSIS:
      precisionExtractor = new ValueAnalysisPrecisionExtractor();
      outputStateBuilder = new ValueAnalysisOutputStateBuilder();
      break;
    case PREDICATEANALYSIS:
      precisionExtractor = new PredicateAnalysisPrecisionExtractor();
      outputStateBuilder = new PredicateOutputStateBuilder();
      break;
    default:
      precisionExtractor = new ValueAnalysisPrecisionExtractor();
      outputStateBuilder = new ValueAnalysisOutputStateBuilder();
    }
  }

  public static IncrementalCache getInstance() {
    if (instance == null) {
      instance = new IncrementalCache();
    }
    return instance;
  }

  public Pair<OneFileStore, ARGState>isCacheHits(Block block, Precision precisionKey, AbstractState inputState) {
    isCacheHitTimer.start();
    String funName = block.getFunctionName();
    if(funName.startsWith("loop") && !CPAMain.loopSummary) {
      isCacheHitTimer.stop();
      return Pair.of(null, null);
    }
    PrecisionHelpState pHelpState = new PrecisionHelpState(funName, precisionKey, precisionExtractor);

    if (!lastVMemoryCache.containsKey(pHelpState) && lastVFileCache.containsKey(pHelpState)) {
      List<OneFileStore> summarys = lastVFileCache.get(pHelpState);
      Map<EqualHelpState, OneFileStore> curMap = new HashMap<>(1);
      for (OneFileStore curFileStore : summarys) {
        try {
          curMap.put(EqualHelpState.buildEqualHelpState(OneFileStore.getRealState(curFileStore.getInputState()), funName),
              curFileStore);
        } catch (IllegalArgumentException illegalArgumentException) {
          System.out.println("From booleanformula to BDD, illegal argument exception......");
          isCacheHitTimer.stop();
          return Pair.of(null, null);
        }
      }
      lastVMemoryCache.put(pHelpState, curMap);
      if(CPAMain.isSubgraph) {
        lastVMemorySubgraph.put(pHelpState, lastVFileSubgraph.get(pHelpState));
      }
    }

    if (lastVMemoryCache.containsKey(pHelpState)) {
      Map<EqualHelpState, OneFileStore> curMap = lastVMemoryCache.get(pHelpState);
      ARGState curSubgraph;
      if(CPAMain.isSubgraph && lastVMemorySubgraph.get(pHelpState) != null) {
        curSubgraph = ((ARGState) lastVMemorySubgraph.get(pHelpState));
      } else {
        curSubgraph = null;
      }
      AbstractState inputRealState = OneFileStore.getRealState(inputState);
      EqualHelpState equalHelpState = EqualHelpState.buildEqualHelpState(inputRealState, funName);
      if (curMap.containsKey(equalHelpState)) {
        isCacheHitTimer.stop();
        logger.log(Level.INFO, "cache hits - " + curMap.get(equalHelpState));
        return Pair.of(curMap.get(equalHelpState), curSubgraph);
      }
    }
    isCacheHitTimer.stop();
    return Pair.of(null,null);
  }

  public void put(AbstractState stateKey, Precision precisionKey, Block context, Collection<AbstractState> item,
      ReachedSet subgraph) {
    AbstractState lastState = null;
    if(item.size() == 0)
      return;
    if(CPAMain.cancelBAM) {
      lastState = item.iterator().next();
    } else {
      lastState = subgraph.getLastState();
    }
    if (CPAMain.summaryOutputPath != null && OneFileStore.canStore(context, lastState) && item.size() > 0) {//save summary
      if (context.getFunctionName() == null) {
        System.out.println("put cache, function name == null");
      }
      if (context.getFunctionName().equals(CPAMain.entryFunction)) {//context.getFunctionName().equals("error") || context.getFunctionName().equals("ldv_error") ||
        return;
      }

      PrecisionHelpState curPHState =
          new PrecisionHelpState(context.getFunctionName(), precisionKey, precisionExtractor);
      EqualHelpState curEHState = EqualHelpState.buildEqualHelpState(OneFileStore.getRealState(stateKey), context.getFunctionName());

      if (lastVMemoryCache.containsKey(curPHState)) {
        if (lastVMemoryCache.get(curPHState).containsKey(curEHState)) { return; }
      }

      if (curVMemoryCache.containsKey(curPHState)) {
        Map<EqualHelpState, OneFileStore> funCached = curVMemoryCache.get(curPHState);
        OneFileStore fileStore = new OneFileStore(context.getFunctionName(), stateKey, item);
        if (!funCached.containsKey(curEHState)) {
          funCached.put(curEHState, fileStore);
        }
        else {
          //System.out.println("contains same equal help state.......");
        }
      }
      else {
        Map<EqualHelpState, OneFileStore> funCached = new HashMap<>(1);
        OneFileStore fileStore = new OneFileStore(context.getFunctionName(), stateKey, item);
        funCached.put(curEHState, fileStore);
        curVMemoryCache.put(curPHState, funCached);
        if(CPAMain.isSubgraph) {
          curVMemorySubgraph.put(curPHState, subgraph.getFirstState());
        }
      }
    }
  }

  public void remove(AbstractState stateKey, Precision precisionKey, Block context) {
    Map<EqualHelpState, OneFileStore> map =
        curVMemoryCache.get(new PrecisionHelpState(context.getFunctionName(), precisionKey, precisionExtractor));
    if (map == null) { return; }
    EqualHelpState helpState = EqualHelpState.buildEqualHelpState(OneFileStore.getRealState(stateKey), context.getFunctionName());
    map.remove(helpState);
  }

  public void loadSummaryFlow() {
    ProgramInfo.getInstance().initProgramDiff();
    //TODO implement resolveSummary for valueAnalysis
    if(CPAMain.isUesTextSummary  || precisionExtractor.getClass().toGenericString().contains("Value")){
      loadSummaryFromFile(CPAMain.summaryInputPath);
      //resolveSummary_test(CPAMain.summaryInputPath);
    } else {
      resolveSummary(CPAMain.summaryInputPath);
    }
//    for (Entry<PrecisionHelpState, List<OneFileStore>> curEntry : lastVFileCache.entrySet()) {
//      if(curEntry.getKey().getFunName().startsWith("loop"))
//        lastVCanUseLoopSummarySize += curEntry.getValue().size();
//      lastVCanUseSummarySize += curEntry.getValue().size();
//    }
//    Set summary_via_text = ((HashMap) lastVFileCache).entrySet();
//    Set summary_via_stream = ((HashMap) lastVFileCache_test).entrySet();
//    for (Object s:summary_via_text
//         ) {
//      if(!summary_via_stream.contains(s)) {
//        throw new UnsupportedOperationException();
//      }
//    }
    System.out.println("load summary ok!");
  }

  private Map<PrecisionHelpState, List<OneFileStore>> mergeSummary() {
    Map<PrecisionHelpState, List<OneFileStore>> curVFileCache = new HashMap<>();
    for (Entry<PrecisionHelpState, Map<EqualHelpState, OneFileStore>> curEntry : lastVMemoryCache.entrySet()) {
      List<OneFileStore> curSum = new ArrayList<>(1);
      for (Entry<EqualHelpState, OneFileStore> curSummaryEntry : curEntry.getValue().entrySet()) {
        curSum.add(curSummaryEntry.getValue());
      }
      curVFileCache.put(curEntry.getKey(), curSum);
    }
    for (Entry<PrecisionHelpState, Map<EqualHelpState, OneFileStore>> curEntry : curVMemoryCache.entrySet()) {
      if (!curVFileCache.containsKey(curEntry.getKey())) {
        List<OneFileStore> curSum = new ArrayList<>(1);
        for (Entry<EqualHelpState, OneFileStore> curSummaryEntry : curEntry.getValue().entrySet()) {
          curSum.add(curSummaryEntry.getValue());
        }
        curVFileCache.put(curEntry.getKey(), curSum);
      }
      else {
        List<OneFileStore> curSum = curVFileCache.get(curEntry.getKey());
        Map<EqualHelpState, OneFileStore> lastVCache = lastVMemoryCache.get(curEntry.getKey());
        for (Entry<EqualHelpState, OneFileStore> curSummaryEntry : curEntry.getValue().entrySet()) {
          if (!lastVCache.containsKey(curSummaryEntry.getKey())) {
            curSum.add(curSummaryEntry.getValue());
          }
        }
      }
    }

    if (!CPAMain.isReusePrecision) {
      for (Entry<PrecisionHelpState, List<OneFileStore>> lastFileEntry : lastVFileCache.entrySet()) {
        if (!curVFileCache.containsKey(lastFileEntry.getKey())) {
          curVFileCache.put(lastFileEntry.getKey(), lastFileEntry.getValue());
        }
      }
    }
    return curVFileCache;
  }

  private List<BooleanFormula> extractFormulas(Precision precision, String funName) {
    PredicateAnalysisPrecisionExtractor pAPrecisionExtractor =
        (PredicateAnalysisPrecisionExtractor) precisionExtractor;
    List<BooleanFormula> formulas = pAPrecisionExtractor.extractPrecision(precision, funName);
    return formulas;
  }

  public void serializeSummary(String filePath, UnmodifiableReachedSet reached) {
    writeFileTimer.start();
    Map<PrecisionHelpState, List<OneFileStore>> curVFileCache = mergeSummary();

    File pathFile = new File(filePath);
    if (!pathFile.exists()) {
      pathFile.mkdirs();
    }
    File termFile = new File(filePath + "/term");
    File dictionaryFile = new File(filePath + "/dictionary");

    //just save newest precision
    Set<PrecisionHelpState> newestPrecisions = precisionExtractor.getNewestPrecision(reached);
    FormulaManager manager = GlobalInfo.getInstance().getFormulaManager();

    try (DataOutputStream out = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(termFile)))) {
      manager.setOutputStream(out, dictionaryFile);
      int needSaveSummaryNum = 0;
      for (Entry<PrecisionHelpState, List<OneFileStore>> curEntry : curVFileCache.entrySet()) {
        if (!CPAMain.isReusePrecision || newestPrecisions.size() == 0 || newestPrecisions.contains(curEntry.getKey())) {
          needSaveSummaryNum++;
        }
      }

      IOUtil.writeVInt(out, needSaveSummaryNum);
      for (Entry<PrecisionHelpState, List<OneFileStore>> curEntry : curVFileCache.entrySet()) {
        if (!CPAMain.isReusePrecision || newestPrecisions.size() == 0 || newestPrecisions.contains(curEntry.getKey())) {
          String funName = curEntry.getKey().getFunName();
          int funNameInt = manager.addSerializeDictionary(FormulaManager.FVARTYPE, funName);
          IOUtil.writeVInt(out, funNameInt);

          List<BooleanFormula> pTerms = extractFormulas(curEntry.getKey().getPrecision(), funName);
          IOUtil.writeVInt(out, pTerms.size());
          for(int i = 0; i < pTerms.size(); i++) {
            manager.serializeFormula(pTerms.get(i));
          }

          List<OneFileStore> curPairs = curEntry.getValue();
          IOUtil.writeVInt(out, curPairs.size());
          for (OneFileStore curStore : curPairs) {
            curStore.serialize(out, manager);
          }
        }
      }
      manager.doneSerializeFormula();
    } catch (FileNotFoundException e1) {
      e1.printStackTrace();
    } catch (IOException e1) {
      e1.printStackTrace();
    }

    writeFileTimer.stop();
  }

  public void resolveSummary(String filePath) {
    readFileTimer.start();
    if (filePath == null) { return; }
    File termFile = new File(filePath + "/term");
    File dictionaryFile = new File(filePath + "/dictionary");
    if (!termFile.exists() || !dictionaryFile.exists()) {
      System.out.println("Summary File Not exist!!!");
      return;
    }

    FormulaManager manager = GlobalInfo.getInstance().getFormulaManager();

    try (DataInputStream in = new DataInputStream(new BufferedInputStream(new FileInputStream(termFile)))) {
      manager.setInputStream(in, dictionaryFile);
      int summaryNum = IOUtil.readVInt(in);
      for (int i = 0; i < summaryNum; i++) {
        int funNameInt = IOUtil.readVInt(in);
        String funName = manager.getResolveDictionary(FormulaManager.FVARTYPE, funNameInt);

        int pFormulaSize = IOUtil.readVInt(in);
        StringBuilder precisionBuilder = new StringBuilder();
        for(int j = 0; j < pFormulaSize; j++) {
          manager.resolveFormula(precisionBuilder);
          if(j != pFormulaSize - 1) {
            precisionBuilder.append(',');
          }
        }

        int pairSize = IOUtil.readVInt(in);
        BAMCache.lastVersionCache += pairSize;
        List<OneFileStore> pairStores = new ArrayList<>(pairSize);
        for (int j = 0; j < pairSize; j++) {
          OneFileStore curStore = OneFileStore.resolve(funName, in, manager);
          pairStores.add(curStore);
        }
        if (ProgramInfo.getInstance().getUnchangedFunSet().contains(funName)) {
          if(!(CPAMain.onlyLoopSummary && !funName.startsWith("loop"))) {
            lastVFileCache.put(new PrecisionHelpState(funName, precisionBuilder.toString()), pairStores);
          }
        }
      }
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }

    readFileTimer.stop();
  }

  public void resolveSummary_test(String filePath) {
    readFileTimer.start();
    if (filePath == null) { return; }
    File termFile = new File(filePath + "/term");
    File dictionaryFile = new File(filePath + "/dictionary");
    if (!termFile.exists() || !dictionaryFile.exists()) {
      System.out.println("Summary File Not exist!!!");
      return;
    }

    FormulaManager manager = GlobalInfo.getInstance().getFormulaManager();

    try (DataInputStream in = new DataInputStream(new BufferedInputStream(new FileInputStream(termFile)))) {
      manager.setInputStream(in, dictionaryFile);
      int summaryNum = IOUtil.readVInt(in);
      for (int i = 0; i < summaryNum; i++) {
        int funNameInt = IOUtil.readVInt(in);
        String funName = manager.getResolveDictionary(FormulaManager.FVARTYPE, funNameInt);

        int pFormulaSize = IOUtil.readVInt(in);
        StringBuilder precisionBuilder = new StringBuilder();
        for(int j = 0; j < pFormulaSize; j++) {
          manager.resolveFormula(precisionBuilder);
          if(j != pFormulaSize - 1) {
            precisionBuilder.append(',');
          }
        }

        int pairSize = IOUtil.readVInt(in);
        BAMCache.lastVersionCache += pairSize;
        List<OneFileStore> pairStores = new ArrayList<>(pairSize);
        for (int j = 0; j < pairSize; j++) {
          OneFileStore curStore = OneFileStore.resolve(funName, in, manager);
          pairStores.add(curStore);
        }
        if (ProgramInfo.getInstance().getUnchangedFunSet().contains(funName)) {
          if(!(CPAMain.onlyLoopSummary && !funName.startsWith("loop"))) {
            lastVFileCache_test.put(new PrecisionHelpState(funName, precisionBuilder.toString()),
                pairStores);
          }
        }
      }
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    }

    readFileTimer.stop();
  }

  public void saveSummaryToFile(String filePath, UnmodifiableReachedSet reached) {
    writeFileTimer.start();
    Map<PrecisionHelpState, List<OneFileStore>> curVFileCache = mergeSummary();

    File pathFile = new File(filePath);
    if (!pathFile.exists()) {
      pathFile.mkdirs();
    }
    File file = new File(filePath + "/summary.txt");
    GlobalInfo.getInstance().summary_fs = file.length();
    File subgraph_file = new File(filePath + "/subgraph.txt");

    try (FileWriter fileWriter = new FileWriter(file);
        BufferedWriter writer = new BufferedWriter(fileWriter)) {
      //just save newest precision
      Set<PrecisionHelpState> newestPrecisions = precisionExtractor.getNewestPrecision(reached);

      for (Entry<PrecisionHelpState, List<OneFileStore>> curEntry : curVFileCache.entrySet()) {
        if(CPAMain.onlyLoopSummary && !curEntry.getKey().getFunName().startsWith("loop")) {
          continue;
        }
        if (!CPAMain.isReusePrecision || newestPrecisions.size() == 0 || newestPrecisions.contains(curEntry.getKey())) {
          writer.write(FUNCTIONLINE + curEntry.getKey());//function name and precision
          List<OneFileStore> curPairs = curEntry.getValue();
          for (OneFileStore curSummary : curPairs) {
            curSummary.saveToFile(writer);
          }
        }
      }
      writer.flush();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    if(CPAMain.isSubgraph) {
      try (FileOutputStream fileWriter = new FileOutputStream(subgraph_file);
           ObjectOutputStream writer = new ObjectOutputStream(fileWriter)) {
        //just save newest precision
        Set<PrecisionHelpState> newestPrecisions = precisionExtractor.getNewestPrecision(reached);

        for (Entry<PrecisionHelpState, AbstractState> curEntry : curVMemorySubgraph.entrySet()) {
          if (!CPAMain.isReusePrecision || newestPrecisions.size() == 0 || newestPrecisions.contains(curEntry.getKey())) {
            //writer.write(FUNCTIONLINE + curEntry.getKey());//function name and precision
            //Set<ARGState> subgraph = ((ARGState)curEntry.getValue()).getSubgraph();
            writer.writeObject(FUNCTIONLINE + curEntry.getKey().toString());
            //for (ARGState state : subgraph) {
            //curSummary.saveToFile(writer);
            writer.writeObject(curEntry.getValue());
            writer.writeObject(null);
            //}
          }
        }
        writer.writeObject(null);
        writer.flush();
      } catch (IOException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    writeFileTimer.stop();
  }

  public void loadSummaryFromFile(String filePath) {
    readFileTimer.start();
    if (filePath == null) { return; }
    File file = new File(filePath + "/summary.txt");
    if (!file.exists()) { return; }
    try (FileReader fileReader = new FileReader(file);
        BufferedReader bufferedReader = new BufferedReader(fileReader)) {
      String curLine = bufferedReader.readLine();
      String curPrecision = null;
      String curFunName = null;
      String curInput = null;
      Collection<Pair<String, Integer>> curOutput = new ArrayList<>();
      Integer curOutputLocation = null;
      String curOthers = null;
      StringBuilder curBuilder = new StringBuilder();
      List<OneFileStore> curFunReturnCache = new ArrayList<>(1);
      while (curLine != null) {

        if (curLine.trim().equals("")) {
          curLine = bufferedReader.readLine();
          continue;
        }
        if (curLine.contains(FUNCTIONLINE)) {

          if (curFunName != null) {
            if (ProgramInfo.getInstance().getUnchangedFunSet().contains(curFunName)) {
              //if(!(CPAMain.onlyLoopSummary && !curFunName.startsWith("loop"))) {
                lastVFileCache.put(new PrecisionHelpState(curFunName, curPrecision), curFunReturnCache);
              //}
            }
            curFunReturnCache = new ArrayList<>(1);
            curOutput = new ArrayList<>(1);
            curPrecision = null;
            curInput = null;
            curOthers = null;
          }
          curFunName = curLine.replace(FUNCTIONLINE, "");
        }
        else if (curLine.equals(PrecisionExtractor.PRECISIONBEGIN.replace("\n", ""))) {
        }
        else if (curLine.equals(PrecisionExtractor.PRECISIONEND.replace("\n", ""))) {
          curPrecision = curBuilder.toString();
          curBuilder.setLength(0);
        }
        else if (curLine.equals(OneFileStore.INPUTSTATEBEGIN)) {
        }
        else if (curLine.equals(OneFileStore.INPUTSTATEEND)) {
          curInput = curBuilder.toString();
          curBuilder.setLength(0);
          BAMCache.lastVersionCache++;
        }
        else if (curLine.equals(OneFileStore.OUTPUTSTATEBEGIN)) {
        }
        else if(curLine.startsWith(OneFileStore.OUTPUTLOCATION)){
          curOutputLocation = Integer.parseInt(curLine.substring(OneFileStore.OUTPUTLOCATION.length()));
        }
        else if (curLine.equals(OneFileStore.OUTPUTSTATEEND)) {
          String tmp = curBuilder.toString();
          curBuilder.setLength(0);
          curOutput.add(Pair.of(tmp, curOutputLocation));
        }
        else if (curLine.equals(OneFileStore.OTHERSBEGIN)) {
        }
        else if (curLine.equals(OneFileStore.OTHERSEND)) {
          String tmp = curBuilder.toString();
          curBuilder.setLength(0);
          curOthers = tmp;

          OneFileStore oneFileStore = OneFileStore.buildFromString(curFunName, curInput, curOutput, curOthers);
          curFunReturnCache.add(oneFileStore);
        }
        else {
          curBuilder.append(curLine + "\n");
        }
        curLine = bufferedReader.readLine();
      }
      if (curPrecision != null) {
        if (ProgramInfo.getInstance().getUnchangedFunSet().contains(curFunName)) {
          //if(!(CPAMain.onlyLoopSummary && !curFunName.startsWith("loop"))) {
            lastVFileCache.put(new PrecisionHelpState(curFunName, curPrecision), curFunReturnCache);
          //}
        }
      }
    } catch (FileNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IOException e) {
      // TODO: handle exception
    }
    if(CPAMain.isSubgraph) {
      file = new File(filePath + "/subgraph.txt");
      if (!file.exists()) {
        return;
      }
      Set<ARGState> subgraph = new HashSet<>();
      try (FileInputStream fileReader = new FileInputStream(file);
           ObjectInputStream reader = new ObjectInputStream(fileReader)) {
        while (true) {
          String phStr = (String) reader.readObject();
          if (phStr == null) {
            break;
          }
          String curPrecision = null;
          String curFunName = null;
          StringBuilder curBuilder = new StringBuilder();
          for (String curLine : phStr.split("\n")) {
            if (curLine.contains(FUNCTIONLINE)) {
              curFunName = curLine.replace(FUNCTIONLINE, "");
            } else if (curLine.equals(PrecisionExtractor.PRECISIONBEGIN.replace("\n", ""))) {
            } else if (curLine.equals(PrecisionExtractor.PRECISIONEND.replace("\n", ""))) {
              curPrecision = curBuilder.toString();
              curBuilder.setLength(0);
            } else {
              curBuilder.append(curLine + "\n");
            }
          }
          PrecisionHelpState precisionHelpState = new PrecisionHelpState(curFunName, curPrecision);
          ARGState state = (ARGState) reader.readObject();
          lastVFileSubgraph.put(precisionHelpState, state);
          reader.readObject();
        }
      } catch (FileNotFoundException e) {
        e.printStackTrace();
      } catch (IOException e) {
        e.printStackTrace();
      } catch (ClassNotFoundException e) {
        e.printStackTrace();
      }
    }

    readFileTimer.stop();
  }

  public Map<PrecisionHelpState, Map<EqualHelpState, OneFileStore>> getCurVFileCache() {
    return lastVMemoryCache;
  }

  public void setCurVFileCache(Map<PrecisionHelpState, Map<EqualHelpState, OneFileStore>> pCurVFileCache) {
    lastVMemoryCache = pCurVFileCache;
  }

  public int getLastVCanUseSummarySize() {
    return lastVCanUseSummarySize;
  }

  public void setLastVCanUseSummarySize(int pLastVCanUseSummarySize) {
    lastVCanUseSummarySize = pLastVCanUseSummarySize;
  }

  public boolean isLoaded() {
    return isLoaded;
  }

  public void setLoaded(boolean pIsLoaded) {
    isLoaded = pIsLoaded;
  }

  public OutputStateBuilder getOutputStateBuilder() {
    return outputStateBuilder;
  }

  public void setOutputStateBuilder(OutputStateBuilder pOutputStateBuilder) {
    outputStateBuilder = pOutputStateBuilder;
  }

  public boolean isCanUseFileCache() {
    return canUseFileCache;
  }

  public void setCanUseFileCache(boolean pCanUseFileCache) {
    canUseFileCache = pCanUseFileCache;
  }

  public Timer getIsCacheHitTimer() {
    return isCacheHitTimer;
  }

  public void setIsCacheHitTimer(Timer pIsCacheHitTimer) {
    isCacheHitTimer = pIsCacheHitTimer;
  }


  public Timer getReadFileTimer() {
    return readFileTimer;
  }


  public void setReadFileTimer(Timer pReadFileTimer) {
    readFileTimer = pReadFileTimer;
  }


  public Timer getWriteFileTimer() {
    return writeFileTimer;
  }

  public void clearSummaryCache() {
    lastVFileCache.clear();
    lastVMemoryCache.clear();
    // curVMemoryCache.clear();
  }

  public void setWriteFileTimer(Timer pWriteFileTimer) {
    writeFileTimer = pWriteFileTimer;
  }
}
