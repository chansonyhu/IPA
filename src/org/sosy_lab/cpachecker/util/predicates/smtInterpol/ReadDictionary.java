package org.sosy_lab.cpachecker.util.predicates.smtInterpol;

import java.io.BufferedInputStream;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

class ReadDictionary {
	private Map<Integer, String> keyMap;
	private Map<Integer, String> fvarMap;
	private Map<Integer, String> cseMap;
	private int keyNum = 0;
	private int fvarNum = 0;
	private int cseNum = 0;

	public ReadDictionary(File file) throws IOException {
		keyMap = new HashMap<>();
		fvarMap = new HashMap<>();
		cseMap = new HashMap<>();
		initFromFile(file);
	}

	public ReadDictionary(File file, int keySize, int fvarSize, int cseSize) throws IOException {
		keyMap = new HashMap<>(keySize);
		fvarMap = new HashMap<>(fvarSize);
		cseMap = new HashMap<>(cseSize);
		initFromFile(file);
	}

	public String getKeyValue(int key) {
		return keyMap.get(key);
	}

	public String getFvarValue(int key) {
		return fvarMap.get(key);
	}

	public String getCseValue(int key) {
		return cseMap.get(key);
	}

	private void initFromFile(File file) throws IOException {
		DataInputStream in = new DataInputStream(new BufferedInputStream(new FileInputStream(file)));
		keyNum = IOUtil.readVInt(in);
		for(int i = 0; i < keyNum; i++) {
			int key = IOUtil.readVInt(in);
			int length = IOUtil.readVInt(in);
			byte[] value = new byte[length];
			in.read(value);
			keyMap.put(key, new String(value));
		}

		fvarNum = IOUtil.readVInt(in);
		for(int i = 0; i < fvarNum; i++) {
			int key = IOUtil.readVInt(in);
			int length = IOUtil.readVInt(in);
			byte[] value = new byte[length];
			in.read(value);
			fvarMap.put(key, new String(value));
		}

		cseNum = IOUtil.readVInt(in);
		for(int i = 0; i < cseNum; i++) {
			int key = IOUtil.readVInt(in);
			int length = IOUtil.readVInt(in);
			byte[] value = new byte[length];
			in.read(value);
			cseMap.put(key, new String(value));
		}

		in.close();
	}
}
