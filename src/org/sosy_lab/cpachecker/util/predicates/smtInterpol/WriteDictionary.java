package org.sosy_lab.cpachecker.util.predicates.smtInterpol;

import java.io.BufferedOutputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

class WriteDictionary {
	private Map<String, Integer> keyMap;//byte:0
	private Map<String, Integer> fvarMap;//byte:1
	private Map<String, Integer> cseMap;//byte:2
	private int keyNum = 0;
	private int fvarNum = 0;
	private int cseNum = 0;

	private File file;

	public WriteDictionary(File file) {
		keyMap = new HashMap<>();
		fvarMap = new HashMap<>();
		cseMap = new HashMap<>();
		this.file = file;
	}

	public WriteDictionary(File file, int keySize, int fvarSize, int cseSize) {
		keyMap = new HashMap<>(keySize);
		fvarMap = new HashMap<>(fvarSize);
		cseMap = new HashMap<>(cseSize);
		this.file = file;
	}

	public int addKeyMap(String value) {
		if(keyMap.containsKey(value)) {
			return keyMap.get(value);
		}
		keyMap.put(value, keyNum++);
		return keyNum - 1;
	}

	public int addFvarMap(String value) {
		if(fvarMap.containsKey(value)) {
			return fvarMap.get(value);
		}
		fvarMap.put(value, fvarNum++);
		return fvarNum - 1;
	}

	public int addCseMap(String value) {
		if(cseMap.containsKey(value)) {
			return cseMap.get(value);
		}
		cseMap.put(value, cseNum++);
		return cseNum - 1;
	}

	public void saveToFile() throws IOException {
		DataOutputStream out = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(file)));
		IOUtil.writeVInt(out, keyNum);
		for(Entry<String, Integer> curE : keyMap.entrySet()) {
			IOUtil.writeVInt(out, curE.getValue());
			byte[] curK = curE.getKey().getBytes();
			int length = curK.length;
			IOUtil.writeVInt(out, length);
			out.write(curK);
		}

		IOUtil.writeVInt(out, fvarNum);
		for(Entry<String, Integer> curE : fvarMap.entrySet()) {
			IOUtil.writeVInt(out, curE.getValue());
			byte[] curK = curE.getKey().getBytes();
			int length = curK.length;
			IOUtil.writeVInt(out, length);
			out.write(curK);
		}

		IOUtil.writeVInt(out, cseNum);
		for(Entry<String, Integer> curE : cseMap.entrySet()) {
			IOUtil.writeVInt(out, curE.getValue());
			byte[] curK = curE.getKey().getBytes();
			int length = curK.length;
			IOUtil.writeVInt(out, length);
			out.write(curK);
		}
		out.close();
	}

}
