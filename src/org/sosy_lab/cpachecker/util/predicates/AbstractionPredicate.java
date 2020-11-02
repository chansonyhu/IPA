/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
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
package org.sosy_lab.cpachecker.util.predicates;

import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedHelper;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;

import com.google.common.base.Preconditions;
import org.sosy_lab.cpachecker.util.predicates.interfaces.RegionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.basicimpl.AbstractFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.SmtInterpolEnvironment;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.SmtInterpolFormulaManager;

import javax.annotation.Nullable;
import java.io.*;

import static com.google.common.base.Preconditions.checkArgument;

/**
 * A generic representation of a predicate
 */
public class AbstractionPredicate implements Externalizable {

  private @Nullable transient Region abstractVariable; // Null after de-serializing from proof
  private BooleanFormula symbolicVariable;
  private BooleanFormula symbolicAtom;
  private int variableNumber;

  AbstractionPredicate(Region pAbstractVariable,
      BooleanFormula pSymbolicVariable, BooleanFormula pSymbolicAtom,
      int variableNumber) {
    abstractVariable = Preconditions.checkNotNull(pAbstractVariable);
    symbolicVariable = Preconditions.checkNotNull(pSymbolicVariable);
    symbolicAtom = Preconditions.checkNotNull(pSymbolicAtom);
    this.variableNumber = variableNumber;
  }

  public AbstractionPredicate() {
    abstractVariable = null;
    symbolicVariable = null;
    symbolicAtom = null;
    variableNumber = -1;
  }

  /**
   * Returns an formula representing this predicate.
   *
   * @return an abstract formula
   */
  public Region getAbstractVariable() {
    return abstractVariable;
  }

  public BooleanFormula getSymbolicVariable() {
    return symbolicVariable;
  }

  public BooleanFormula getSymbolicAtom() {
    return symbolicAtom;
  }

  @Override
  public boolean equals(Object pObj) {
    if (pObj == this) {
      return true;
    } else if (!(pObj instanceof AbstractionPredicate)) {
      return false;
    } else {
      AbstractionPredicate other = (AbstractionPredicate)pObj;
      //TODO qianshan may be not complete
      try {
        this.abstractVariable.toString();
        other.abstractVariable.toString();
      } catch (NullPointerException npe) {
        //System.out.println("AbstractionPredicate imprecise equal");
        return //this.symbolicVariable.equals(other.symbolicVariable) &&
            this.symbolicAtom.equals(other.symbolicAtom);
                //&& variableNumber == other.variableNumber;
      }
      if((this.abstractVariable == null || other.abstractVariable == null) && CPAMain.isReuseInvariant) {
        //System.out.println("AbstractionPredicate imprecise equal");
        return //this.symbolicVariable.equals(other.symbolicVariable) &&
                this.symbolicAtom.equals(other.symbolicAtom); //&& this.symbolicVariable.equals(other.symbolicVariable)
            //&& variableNumber == other.variableNumber;
      }
      return this.abstractVariable.equals(other.abstractVariable);
    }
  }

  @Override
  public int hashCode() {
    return symbolicAtom.hashCode();
    //return abstractVariable.hashCode();
  }

  @Override
  public String toString() {
    try{
      abstractVariable.toString();
    } catch (NullPointerException npe) {
      return "null<->" + symbolicVariable + " <-> " + symbolicAtom;
    }
    return abstractVariable + " <-> " + symbolicVariable + " <-> " + symbolicAtom;
  }

  public int getVariableNumber() {
    return variableNumber;
  }

  @Override
  public void writeExternal(ObjectOutput out) throws IOException {
//    checkArgument(out instanceof DataOutputStream);
//    SmtInterpolFormulaManager fmgr = (SmtInterpolFormulaManager) GlobalInfo.getInstance().getFormulaManager();
//    File dictionaryFile = new File(filePath + "/dictionary");
//    fmgr.setOutputStream((DataOutputStream) out, dictionaryFile);
//    fmgr.serializeFormula(symbolicVariable);
//    fmgr.serializeFormula(symbolicAtom);
    RegionManager rmgr = GlobalInfo.getInstance().getRegionManager();

    out.writeObject(abstractVariable);
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
    out.writeObject(formulaManagerView.dumpFormula(symbolicVariable).toString());
    out.writeObject(formulaManagerView.dumpFormula(symbolicAtom).toString());

    out.writeInt(variableNumber);
  }

  @Override
  public void readExternal(ObjectInput in) throws IOException, ClassNotFoundException {
//    SmtInterpolFormulaManager fmgr = (SmtInterpolFormulaManager) GlobalInfo.getInstance().getFormulaManager();
//    fmgr.resolveFormula();
    checkArgument(abstractVariable == null);
    checkArgument(symbolicVariable == null);
    checkArgument(symbolicAtom == null);
    checkArgument(variableNumber == -1);
    abstractVariable = (Region) in.readObject();
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
    String symbolicVariableStr = (String) in.readObject();
    symbolicVariable = formulaManagerView.parse(symbolicVariableStr);
    String symbolicAtomStr = (String) in.readObject();
    symbolicAtom = formulaManagerView.parse(symbolicAtomStr);
    variableNumber = in.readInt();
//    name = (String)in.readObject();
//    age = in.readInt();
  }
}
