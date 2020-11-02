package org.sosy_lab.cpachecker.util.predicates.smtInterpol;

import java.io.DataInputStream;
import java.io.File;
import java.io.IOException;

public class ResolveTerm {
	private DataInputStream in;
	private ReadDictionary dictionary;

	private static byte[] appTermType = new byte[1];
	private static byte[] constTermType = new byte[1];
	private static byte[] letTermType = new byte[1];
	private static byte[] termVarType = new byte[1];

	static {
		appTermType[0] = 3;
		constTermType[0] = 4;
		letTermType[0] = 5;
		termVarType[0] = 6;
	}

	public ResolveTerm(DataInputStream in, File dictionaryFile) throws IOException {
		this.in = in;
		this.dictionary = new ReadDictionary(dictionaryFile);
	}

	public void close() throws IOException {
		this.in.close();
	}

	public void resolveTerms(final StringBuilder builder) throws IOException {
	  int formulaSize = IOUtil.readVInt(in);
	  for(int i = 0; i < formulaSize; i++) {
	    resolve(builder);
	    if(i != formulaSize - 1) {
        builder.append(',');
      }
	  }
	}

	public void resolve(StringBuilder builder) throws IOException {
		int defineSize = IOUtil.readVInt(in);
		for(int i = 0; i < defineSize; i++) {
			int funcNameInt = IOUtil.readVInt(in);
			String funcNameStr = dictionary.getFvarValue(funcNameInt);
			builder.append("(declare-fun " + funcNameStr);
			int parasSize = IOUtil.readVInt(in);
			builder.append(" (");
			for(int j = 0; j < parasSize; j++) {
				resolveSort(builder);
				if(j != parasSize - 1) {
					builder.append(' ');
				}
			}
			builder.append(") ");
			resolveSort(builder);
			builder.append(")\n");
		}

		//resolve term
		builder.append("(assert ");
		resolveTerm(builder);
		builder.append(')');
	}

	private void resolveTerm(StringBuilder builder) throws IOException {
		byte[] type = new byte[1];
		in.read(type);
		if(type[0] == appTermType[0]) {
			int argsSize = IOUtil.readVInt(in);
			if(argsSize == 0) {
				int funInt = IOUtil.readVInt(in);
				String func = dictionary.getFvarValue(funInt);
				builder.append(func);
				return;
			}
			else {
				builder.append('(');
				StringBuilder argsBuilder = new StringBuilder();
				for(int i = 0; i < argsSize; i++) {
					resolveTerm(argsBuilder);
					if(i != argsSize - 1) {
            argsBuilder.append(' ');
          }
				}
				int funInt = IOUtil.readVInt(in);
				String func = dictionary.getFvarValue(funInt);
				builder.append(func + " ");
				builder.append(argsBuilder);
				builder.append(')');
			}
		}
		else if(type[0] == constTermType[0]) {
			int length = IOUtil.readVInt(in);
			byte[] bytes = new byte[length];
			in.read(bytes);
			builder.append(new String(bytes));
		}
		else if(type[0] == letTermType[0]) {
			builder.append("(let ((");
			int valueLength = IOUtil.readVInt(in);
			int curValInt = IOUtil.readVInt(in);
			builder.append(dictionary.getCseValue(curValInt) + " ");
			resolveTerm(builder);
			for(int i = 1; i < valueLength; i++) {
				curValInt = IOUtil.readVInt(in);
				builder.append(") (" + dictionary.getCseValue(curValInt) + " ");
				resolveTerm(builder);
			}
			builder.append("))");
			resolveTerm(builder);
			builder.append(")");
		}
		else if(type[0] == termVarType[0]) {
			int cseInt = IOUtil.readVInt(in);
			builder.append(dictionary.getCseValue(cseInt));
		}
		else {
			System.out.println("didn't implement Type:" + type[0]);
			System.exit(-1);
		}
	}

	private void resolveSort(StringBuilder builder) throws IOException {
		int argsSize = IOUtil.readVInt(in);
		if(argsSize == 0) {
			int nameInt = IOUtil.readVInt(in);
			String nameStr = dictionary.getKeyValue(nameInt);
			builder.append(nameStr);
			return;
		}
		builder.append('(');
		StringBuilder argsBuilder = new StringBuilder();
		for(int i = 0; i < argsSize; i++) {
			resolveSort(argsBuilder);
			if(i != argsSize - 1) {
        argsBuilder.append(' ');
      }
		}
		int nameInt = IOUtil.readVInt(in);
		String nameStr = dictionary.getKeyValue(nameInt);
		builder.append(nameStr + " ");
		builder.append(argsBuilder);
		builder.append(')');
	}

	public DataInputStream getIn() {
	  return this.in;
	}

	public String getKeyValue(int key) {
	  return this.dictionary.getKeyValue(key);
	}

	public String getFvarValue(int key) {
	  return this.dictionary.getFvarValue(key);
	}

	public String getCseValue(int key) {
	  return this.dictionary.getCseValue(key);
	}
}
