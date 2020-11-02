package org.sosy_lab.cpachecker.cpa.bam.incremental.program;

public class SimpleDiffer {

  public static boolean functionBodyDiffer(FunctionInfo first, FunctionInfo second) {
    int fLine = first.getLineNum();
    int sLine = second.getLineNum();
    if(fLine != sLine) {
      return false;
    }
    return functionBodyDiffer(first.getFunctionBody(), second.getFunctionBody());
  }

	private static boolean functionBodyDiffer(String fBody, String sBody) {
		String[] fbodyStrings = fBody.split("\\n");
		String[] sbodysStrings = sBody.split("\\n");
		if(fbodyStrings.length != sbodysStrings.length) {
      return false;
    }
		for(int i = 0; i < fbodyStrings.length; i++) {
			if(fbodyStrings[i].contains("#line")) {
        continue;
      } else if(fbodyStrings[i].contains("goto ldv") || (fbodyStrings[i].contains("descriptor") && fbodyStrings[i].contains("lineno"))) {
        continue;
      } else if(fbodyStrings[i].contains("ldv_")) {
        continue;
      } else if(!fbodyStrings[i].equals(sbodysStrings[i])) {
        return false;
      }
		}
		return true;
	}

}
