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

import static com.google.common.base.Preconditions.checkNotNull;

//import com.google.gson.annotations.Expose;
import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.util.Set;

import javax.annotation.Nullable;

import org.sosy_lab.cpachecker.util.UniqueIdGenerator;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;
import org.sosy_lab.cpachecker.util.predicates.interfaces.RegionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;

import com.google.common.collect.ImmutableSet;

/**
 * Instances of this class should hold a state formula (the result of an
 * abstraction computation) in several representations:
 * First, as an abstract region (usually this would be a BDD).
 * Second, as a symbolic formula.
 * Third, again as a symbolic formula, but this time all variables have names
 * which include their SSA index at the time of the abstraction computation.
 *
 * Additionally the formula for the block immediately before the abstraction
 * computation is stored (this also has SSA indices as it is a path formula,
 * even if it is not of the type PathFormula).
 *
 * Abstractions are not considered equal even if they have the same formula.
 */
public class AbstractionFormula implements Serializable {


  private static final long serialVersionUID = -7756517128231447937L;
  private final Region region; // Null after de-serializing from proof
  private final BooleanFormula formula;
  private final BooleanFormula instantiatedFormula;

  /**
   * The formula of the block directly before this abstraction.
   * (This formula was used to create this abstraction).
   */
  private final PathFormula blockFormula;

  private static UniqueIdGenerator idGenerator = new UniqueIdGenerator();
  private final int id = idGenerator.getFreshId();
  private transient BooleanFormulaManager mgr;
  private transient ImmutableSet<Integer> idsOfStoredAbstractionReused;

  public AbstractionFormula(
      FormulaManagerView mgr,
      Region pRegion, BooleanFormula pFormula,
      BooleanFormula pInstantiatedFormula, PathFormula pBlockFormula,
      Set<Integer> pIdOfStoredAbstractionReused) {
    this.mgr = checkNotNull(mgr.getBooleanFormulaManager());
    this.region = checkNotNull(pRegion);
    this.formula = checkNotNull(pFormula);
    this.instantiatedFormula = checkNotNull(pInstantiatedFormula);
    this.blockFormula = checkNotNull(pBlockFormula);
    this.idsOfStoredAbstractionReused = ImmutableSet.copyOf(pIdOfStoredAbstractionReused);
  }

  public boolean isReusedFromStoredAbstraction() {
    return !idsOfStoredAbstractionReused.isEmpty();
  }

  public boolean isTrue() {
    return mgr.isTrue(formula);
  }

  public boolean isFalse() {
    return mgr.isFalse(formula);
  }

  public @Nullable Region asRegion() {
    return region;
  }

  public void clearForSer() {
//    region = null;
//    mgr = null;
//    idsOfStoredAbstractionReused = null;
//    formula = null;
//    idGenerator = null;
  }
  /**
   * Returns the formula representation where all variables do not have SSA indices.
   */
  public BooleanFormula asFormula() {
    return formula;
  }

  /**
   * Returns the formula representation where all variables DO have SSA indices.
   */
  public BooleanFormula asInstantiatedFormula() {
    return instantiatedFormula;
  }

  public PathFormula getBlockFormula() {
    return blockFormula;
  }

  public int getId() {
    return id;
  }

  public ImmutableSet<Integer> getIdsOfStoredAbstractionReused() {
    return idsOfStoredAbstractionReused;
  }

  @Override
  public String toString() {
    // we print the formula only when it is small
    String abs = "";
    if (isTrue()) {
      abs = ": true";
    } else if (isFalse()) {
      abs = ": false";
    }
    // yqs17: print all the formula
    String raw = this.formula.toString();
    abs = raw;
    return "ABS" + id + abs;
  }

  public Object writeReplace() {
    return new SerializationProxy(this);
  }

  private void readObject(ObjectInputStream in)
      throws IOException, ClassNotFoundException {
    throw new InvalidObjectException("Proxy required");
  }

  public static class SerializationProxy implements Serializable {
    private static final long serialVersionUID = 2349286L;
    private final Region region;
    private final String formulaDump;
    private final String instantiatedFormulaDump;
    private final PathFormula blockFormula;

    public SerializationProxy(AbstractionFormula pAbstractionFormula) {
      FormulaManagerView mgr = GlobalInfo.getInstance().getFormulaManagerView();
      RegionManager rmgr = GlobalInfo.getInstance().getRegionManager();
      region = rmgr.makeTrue();
      instantiatedFormulaDump = mgr.dumpFormula(
          pAbstractionFormula.asInstantiatedFormula()).toString();
      formulaDump = mgr.dumpFormula(pAbstractionFormula.asFormula()).toString();
      blockFormula = pAbstractionFormula.getBlockFormula();
    }

    private Object readResolve() {
      FormulaManagerView mgr = GlobalInfo.getInstance().getFormulaManagerView();
      BooleanFormula instantiatedFormula = mgr.parse(instantiatedFormulaDump);
      BooleanFormula notInstantiated = mgr.uninstantiate(instantiatedFormula);
      return new AbstractionFormula(
          mgr,
          GlobalInfo.getInstance().getAbstractionManager()
          .buildRegionFromFormulaWithUnknownAtoms(notInstantiated), notInstantiated,
          instantiatedFormula, blockFormula, ImmutableSet.<Integer> of());
    }
  }
}