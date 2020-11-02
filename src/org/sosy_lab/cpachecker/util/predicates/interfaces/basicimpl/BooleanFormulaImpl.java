package org.sosy_lab.cpachecker.util.predicates.interfaces.basicimpl;

import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;

import java.io.Serializable;

/**
 * Simple BooleanFormula implementation.
 */
public class BooleanFormulaImpl<TFormulaInfo> extends AbstractFormula<TFormulaInfo> implements BooleanFormula, Serializable {
  public BooleanFormulaImpl(TFormulaInfo pT) {
    super(pT);
  }
}
