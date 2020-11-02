package org.sosy_lab.cpachecker.cpa.bam.incremental.program;

import static com.google.common.base.Preconditions.checkArgument;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.Paths;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedHelper;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;

public class ProgramDiffer {

	public static HashSet<String> programDiffer(HashMap<String, FunctionInfo> oldFunctionInfos, HashMap<String, FunctionInfo> newFunctionInfos) {
		//TODO qianshan
		if(!CPAMain.loopSummary && CPAMain.onlyFunctionSummary){
			Set<String> loopName;
			loopName = new HashSet<>(oldFunctionInfos.keySet());
			for (String s:loopName
					) {
				if(s.startsWith("loop")){
					oldFunctionInfos.remove(s);
				}
			}
			loopName = new HashSet<>(newFunctionInfos.keySet());
			for (String s:loopName
					) {
				if(s.startsWith("loop")){
					newFunctionInfos.remove(s);
				}
			}
		}
		if(!GlobalInfo.getInstance().cfaInfoPath.equals("")) {
			final String FUNC_MOD = GlobalInfo.getInstance().cfaInfoPrefix + ".func.mod";

			Path func_mod_file = Paths.get(GlobalInfo.getInstance().cfaInfoPath, FUNC_MOD);
			BufferedReader reader;
			try {
				System.out.println(func_mod_file);
				if (!func_mod_file.exists()) {
					System.out.println("func.mod file not found!");
					return new HashSet<>();
				}
				reader = new BufferedReader(new InputStreamReader(
						new FileInputStream(
								func_mod_file.getAbsolutePath()),
						Charset
								.defaultCharset()));
				for (String rawline = reader.readLine(); rawline != null;
				     rawline = reader.readLine()) {
					String tmp = rawline.substring(0, rawline.indexOf("."));
					tmp = tmp.substring(5);
					String func = tmp;
					FunctionInfo curInfo = newFunctionInfos.get(func);
					checkArgument(curInfo != null);
					curInfo.setChanged(true);
				}
			} catch (IOException e) {
				e.printStackTrace();
			}

		} else {
			for (Entry<String, FunctionInfo> curEntry : newFunctionInfos.entrySet()) {
				FunctionInfo curInfo = curEntry.getValue();
				FunctionInfo tmpOldInfo = oldFunctionInfos.get(curInfo.getName());
				if (tmpOldInfo == null) {
					curInfo.setChanged(true);
					continue;
				}

				if (!SimpleDiffer.functionBodyDiffer(tmpOldInfo, curInfo)) {
					curInfo.setChanged(true);
				}
			}
		}

		HashSet<String> resultSet = new HashSet<>();

		FunctionNode mainNode = new FunctionNode(ProgramInfo.getInstance().getMainInfo());
		FCG.createFunctionCallGraphAndUpdateChanges(mainNode, newFunctionInfos);

		for (Entry<String, FunctionInfo> curEntry : newFunctionInfos.entrySet()) {
		  FunctionInfo curInfo = curEntry.getValue();
			if(!curInfo.isChanged()) {
				resultSet.add(curInfo.getName());
			}
		}
		return resultSet;
	}

}
