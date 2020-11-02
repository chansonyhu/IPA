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
package org.sosy_lab.cpachecker.util.globalinfo;

import com.google.common.collect.ImmutableList;
import java.io.Serializable;
import java.util.ArrayList;

import java.util.HashSet;
import java.util.Set;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.core.CPAcheckerResult.Result;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.ConfigurableProgramAnalysis;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.apron.ApronManager;
import org.sosy_lab.cpachecker.cpa.arg.ARGCPA;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.automaton.Automaton;
import org.sosy_lab.cpachecker.cpa.automaton.ControlAutomatonCPA;
import org.sosy_lab.cpachecker.cpa.composite.CompositeCPA;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedCPA;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractionManager;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractionRefinementStrategy.PredicateSharing;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateCPA;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateTransferRelation;
import org.sosy_lab.cpachecker.cpa.predicate.persistence.PredicateMapParser;
import org.sosy_lab.cpachecker.util.UniqueIdGenerator;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.RegionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;

import com.google.common.base.Optional;
import com.google.common.base.Preconditions;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.SmtInterpolBooleanFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.SmtInterpolFormulaCreator;
import org.sosy_lab.cpachecker.util.predicates.z3.Z3FormulaManager;


public class GlobalInfo {
  //the index of ImpactedCPA in the CompositeState
  public final UniqueIdGenerator idGenerator = new UniqueIdGenerator();
  public static ClassLoader classloader;
  public static Integer ImpactedCPAPos = -1;
  public Result result =  Result.NOT_YET_STARTED;
  private static GlobalInfo instance;
  public SmtInterpolFormulaCreator creator;
  private CFAInfo cfaInfo;
  private AutomatonInfo automatonInfo = new AutomatonInfo();
  private ConfigurableProgramAnalysis cpa;
  private FormulaManager formulaManager;
  private FormulaManagerView formulaManagerView;
  private ArrayList<Serializable> helperStorages = new ArrayList<>();
  private AbstractionManager absManager;
  private ApronManager apronManager;
  private RegionManager regionManager;
  private PathFormulaManager pathFormulaManager;
  public PredicateAbstractionManager predicateManager;
  private SmtInterpolBooleanFormulaManager smtBfManager;
  public PredicateTransferRelation pred_trans;
  public PredicateSharing predicateSharing;
  private LogManager logger;
  public Z3FormulaManager z3fm;
  private PathFormula emptyPathFormula;
  public int lastAbstractions = 0;
  public int curAbstractions = 0;
  public String cfaInfoPath = "";
  public String cfaInfoPrefix;
  public PredicateCPA predicateCPA;
  public PredicatePrecision emptyPrecision;
  public long cpuTimeLimit;
  public ReachedSet currentReached;
  public ARGState currentElement;

  public Set<BooleanFormula> predsToRemove = new HashSet<>();

  //file size
  public long summary_fs = 0;
  public long invariant_fs = 0;
  public long predicate_fs = 0;
  public int lastInvSize = -1;

  public int lastPathLength = -1;
  public int spltimes = 0;

  public int umc = 0;
  public final static int MAX_UMC = 300;
  public final static int restart_threshold = 10000;

  public PredicateMapParser predicateMapParser;

  public void storeRegionManager(RegionManager regionManager) {
    this.regionManager = regionManager;
  }

  public RegionManager getRegionManager() {
    return regionManager;
  }

  public PathFormula getEmptyPathFormula() {
    if(emptyPathFormula == null) {
      emptyPathFormula = pathFormulaManager.makeEmptyPathFormula();
      return emptyPathFormula;
    } else {
      return emptyPathFormula;
    }
  }

  public SmtInterpolBooleanFormulaManager getSmtInterpolBooleanFormulaManager() {
    return smtBfManager;
  }

  public void storeSmtInterpolBooleanFormulaManager(SmtInterpolBooleanFormulaManager smtBfManager) {
    this.smtBfManager = smtBfManager;
  }

  public PathFormulaManager getPathFormulaManager() {
    return pathFormulaManager;
  }

  public void storePathFormulaManager(PathFormulaManager pathFormulaManager) {
    this.pathFormulaManager = pathFormulaManager;
  }


  private GlobalInfo() {
    pathFormulaManager = null;
  }

  public static GlobalInfo getInstance() {
    if (instance == null) {
      instance = new GlobalInfo();
    }
    return instance;
  }

  public void storeCFA(CFA cfa) {
    cfaInfo = new CFAInfo(cfa);
  }

  public Optional<CFAInfo> getCFAInfo() {
    return Optional.fromNullable(cfaInfo);
  }

  public void storeAutomaton(Automaton automaton, ControlAutomatonCPA automatonCPA) {
    automatonInfo.register(automaton, automatonCPA);
  }

  public AutomatonInfo getAutomatonInfo() {
    Preconditions.checkState(automatonInfo != null);
    return automatonInfo;
  }

  public void storeCPA(ConfigurableProgramAnalysis cpa) {
    this.cpa = cpa;
    if(cpa instanceof ARGCPA) {
      ImmutableList<ConfigurableProgramAnalysis> wrappedCPAs = ((CompositeCPA) ((ARGCPA) cpa).getWrappedCPAs().get(0)).getWrappedCPAs();
      for(ConfigurableProgramAnalysis pCpa : wrappedCPAs) {
        if(pCpa instanceof ImpactedCPA) {
          ImpactedCPAPos = wrappedCPAs.indexOf(pCpa);
          break;
        }
      }
    }
  }

  public Optional<ConfigurableProgramAnalysis> getCPA() {
    return Optional.fromNullable(cpa);
  }

  public void storeFormulaManager(FormulaManager pFormulaManager) {
    formulaManager = pFormulaManager;
  }

  public void storeFormulaManagerView(FormulaManagerView pFormulaManagerView) {
    formulaManagerView = pFormulaManagerView;
  }

  public void storeAbstractionManager(AbstractionManager absManager) {
    this.absManager = absManager;
  }

  public void storeApronManager(ApronManager pApronManager) {
    apronManager = pApronManager;
  }

  public void storeLogManager(LogManager pLogManager) {
    logger = pLogManager;
  }

  public FormulaManager getFormulaManager() {
    Preconditions.checkState(formulaManager != null);
    return formulaManager;
  }

  public FormulaManagerView getFormulaManagerView() {
    Preconditions.checkState(formulaManagerView != null);
    return formulaManagerView;
  }

  public AbstractionManager getAbstractionManager() {
    // Preconditions.checkState(absManager != null);
    return absManager;
  }

  public ApronManager getApronManager() {
    return apronManager;
  }

  public LogManager getLogManager() {
    return logger;
  }

  public int addHelperStorage(Serializable e) {
    helperStorages.add(e);
    return helperStorages.size() - 1;
  }

  public Serializable getHelperStorage(int index) {
    return helperStorages.get(index);
  }

  public int getNumberOfHelperStorages() {
    return helperStorages.size();
  }

}
