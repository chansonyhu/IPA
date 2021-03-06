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
package org.sosy_lab.cpachecker.util.predicates.interfaces.view;

import org.sosy_lab.cpachecker.util.predicates.interfaces.ArrayFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.ArrayFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Formula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaType;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaType.ArrayFormulaType;

public class ArrayFormulaManagerView
  extends BaseManagerView
  implements ArrayFormulaManager {

  private ArrayFormulaManager manager;

  ArrayFormulaManagerView(FormulaWrappingHandler pWrappingHandler, ArrayFormulaManager pManager) {
    super(pWrappingHandler);
    this.manager = pManager;
  }

  @Override
  public <TI extends Formula, TE extends Formula> TE select (
      ArrayFormula<TI, TE> pArray, Formula pIndex) {

    @SuppressWarnings("unchecked")
    final ArrayFormula<TI, TE> declaredArray = (ArrayFormula<TI, TE>) unwrap(pArray);
    final TE selectResult = manager.select(declaredArray, unwrap(pIndex));
    final FormulaType<TE> resultType = getElementType(pArray);

    // the result of a select can also be a reference to an array! (multi-dimensional arrays)
    // example: returns an array
    return wrap(resultType, selectResult);
  }

  @Override
  public <TI extends Formula, TE extends Formula> ArrayFormula<TI, TE> store (
      ArrayFormula<TI, TE> pArray, Formula pIndex, Formula pValue) {

    @SuppressWarnings("unchecked")
    final ArrayFormula<TI, TE> declaredArray = (ArrayFormula<TI, TE>) unwrap(pArray);

    return manager.store(declaredArray, unwrap(pIndex), unwrap(pValue));
  }

  @SuppressWarnings("unchecked")
  @Override
  public <TI extends Formula, TE extends Formula, FTI extends FormulaType<TI>, FTE extends FormulaType<TE>> ArrayFormula<TI, TE> makeArray(
      String pName, FTI pIndexType, FTE pElementType) {

    final ArrayFormulaType<TI, TE> inputArrayType = new ArrayFormulaType<>(pIndexType, pElementType);
    final FTI unwrappedIndexType = (FTI) unwrapType(pIndexType);
    final FTE unwrappedElementType = (FTE) unwrapType(pElementType);

    final ArrayFormula<TI, TE> result = manager.makeArray(pName, unwrappedIndexType, unwrappedElementType);

    return wrap(inputArrayType, result);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <TI extends Formula, FTI extends FormulaType<TI>> FTI getIndexType(ArrayFormula<TI, ?> pArray) {
    if (pArray instanceof WrappingFormula<?,?>) {
      ArrayFormulaType<?, ?> t = (ArrayFormulaType<?, ?>) ((WrappingFormula<?,?>) pArray).getType();
      return (FTI) t.getIndexType();
    }
    return manager.getIndexType(pArray);
  }

  @SuppressWarnings("unchecked")
  @Override
  public <TE extends Formula, FTE extends FormulaType<TE>> FTE getElementType(ArrayFormula<?, TE> pArray) {
    if (pArray instanceof WrappingFormula<?,?>) {
      ArrayFormulaType<?, ?> t = (ArrayFormulaType<?, ?>) ((WrappingFormula<?,?>) pArray).getType();
      return (FTE) t.getElementType();
    }
    return manager.getElementType(pArray);
  }

  @Override
  public <TI extends Formula, TE extends Formula> BooleanFormula equivalence(ArrayFormula<TI, TE> pArray1,
      ArrayFormula<TI, TE> pArray2) {

    @SuppressWarnings("unchecked")
    final ArrayFormula<TI, TE> declaredArray1 = (ArrayFormula<TI, TE>) unwrap(pArray1);
    @SuppressWarnings("unchecked")
    final ArrayFormula<TI, TE> declaredArray2 = (ArrayFormula<TI, TE>) unwrap(pArray2);

    BooleanFormula result = manager.equivalence(declaredArray1, declaredArray2);
    return wrap(FormulaType.BooleanType, result);
  }

}
