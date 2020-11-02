package org.sosy_lab.cpachecker.util.predicates.smtInterpol;

import java.io.DataOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class SerializeTerm {

  private DataOutputStream out;
  private DataOutputBuffer buffer = new DataOutputBuffer();
  private WriteDictionary dictionary;

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

  public SerializeTerm(DataOutputStream out, File dictionaryFile) throws FileNotFoundException {
    this.out = out;
    this.dictionary = new WriteDictionary(dictionaryFile);
  }

  public void close() throws IOException {
    this.out.close();
  }

  public void append(final List<Term> formulas) throws IOException {
    IOUtil.writeVInt(out, formulas.size());
    for(Term curT : formulas) {
      append(curT);
    }
  }

  public void append(final Term formula) throws IOException {
    Set<Term> seen = new HashSet<>();
    Set<FunctionSymbol> declaredFunctions = new HashSet<>();
    Deque<Term> todo = new ArrayDeque<>();
    int defineSize = 0;

    todo.addLast(formula);

    //write to buffer first, because don't know (decalre-fun)'s size
    while (!todo.isEmpty()) {
      Term t = todo.removeLast();
      while (t instanceof AnnotatedTerm) {
        t = ((AnnotatedTerm) t).getSubterm();
      }
      if (!(t instanceof ApplicationTerm)
          || !seen.add(t)) {
        continue;
      }

      ApplicationTerm term = (ApplicationTerm) t;
      Collections.addAll(todo, term.getParameters());

      FunctionSymbol func = term.getFunction();
      if (func.isIntern()) {
        continue;
      }

      if (func.getDefinition() == null) {
        if (declaredFunctions.add(func)) {
          defineSize++;

          int funcNameInt = dictionary.addFvarMap(PrintTerm.quoteIdentifier(func.getName()));
          IOUtil.writeVInt(buffer, funcNameInt);

          IOUtil.writeVInt(buffer, func.getParameterSorts().length);
          for (Sort paramSort : func.getParameterSorts()) {
            append(paramSort, buffer);
          }
          append(func.getReturnSort(), buffer);
        }
      } else {
        // We would have to print a (define-fun) command and
        // recursively traverse into func.getDefinition() (in post-order!).
        // However, such terms should actually not occur.
        throw new IllegalArgumentException("Terms with definition are unsupported.");
      }
    }

    IOUtil.writeVInt(out, defineSize);
    out.write(buffer.getData(), 0, buffer.getLength());
    buffer.reset();

    Term letted = (new FormulaLet()).let(formula);
    append(letted, out);
  }

  private void append(final Term term, DataOutputStream out) throws IOException {
    if (term instanceof ApplicationTerm) {
      out.write(appTermType);
      ApplicationTerm applicationTerm = (ApplicationTerm) term;
      String func = applicationTerm.getFunction().getApplicationString();
      Term[] args = applicationTerm.getParameters();
      int argsSize = args.length;
      IOUtil.writeVInt(out, argsSize);
      for (Term curT : args) {
        append(curT, out);
      }
      IOUtil.writeVInt(out, dictionary.addFvarMap(func));
    } else if (term instanceof ConstantTerm) {
      out.write(constTermType);
      String constantString = term.toString();
      IOUtil.writeVInt(out, constantString.getBytes().length);
      out.write(constantString.getBytes());
    } else if (term instanceof LetTerm) {
      out.write(letTermType);
      LetTerm letTerm = (LetTerm) term;

      TermVariable[] vars = letTerm.getVariables();
      Term[] values = letTerm.getValues();
      IOUtil.writeVInt(out, vars.length);
      for (int i = 0; i < values.length; i++) {
        IOUtil.writeVInt(out, dictionary.addCseMap(vars[i].toString()));
        append(values[i], out);
      }
      append(letTerm.getSubTerm(), out);
    } else if (term instanceof TermVariable) {
      out.write(termVarType);
      IOUtil.writeVInt(out, dictionary.addCseMap(term.toString()));
    } else {
      System.out.println("didn't implement Term:" + term.getClass());
      System.exit(-1);
    }
  }

  private void append(final Sort sort, DataOutputStream out) throws IOException {
    String name = sort.getIndexedName();
    Sort[] args = sort.getArguments();
    IOUtil.writeVInt(out, args.length);
    for (Sort curS : args) {
      append(curS, out);
    }
    IOUtil.writeVInt(out, dictionary.addKeyMap(name));
  }

  public int addKeyMap(String value) {
    return this.dictionary.addKeyMap(value);
  }

  public int addFvarMap(String value) {
    return this.dictionary.addFvarMap(value);
  }

  public int addCseMap(String value) {
    return this.dictionary.addCseMap(value);
  }

  public void writeDictionary() throws IOException {
    this.dictionary.saveToFile();
  }

  public DataOutputStream getOut() {
    return this.out;
  }
}
