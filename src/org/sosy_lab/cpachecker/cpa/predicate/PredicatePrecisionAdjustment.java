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
package org.sosy_lab.cpachecker.cpa.predicate;

import static com.google.common.base.MoreObjects.firstNonNull;
import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Multimap;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.logging.Level;

import javax.annotation.Nullable;

import com.google.common.collect.ImmutableSet;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.algorithm.CEGARAlgorithm;
import org.sosy_lab.cpachecker.core.algorithm.CEGARAlgorithm.CEGARStatistics;
import org.sosy_lab.cpachecker.core.algorithm.invariants.InvariantGenerator;
import org.sosy_lab.cpachecker.core.algorithm.invariants.InvariantSupplier;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustment;
import org.sosy_lab.cpachecker.core.interfaces.PrecisionAdjustmentResult;
import org.sosy_lab.cpachecker.core.reachedset.UnmodifiableReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.impacted.ImpactedHelper;
import org.sosy_lab.cpachecker.cpa.impacted.IncrementalPAUtil;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState.ComputeAbstractionState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractionRefinementStrategy.PredicateSharing;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.Solver;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;

import com.google.common.base.Function;
import com.google.common.base.Optional;

public class PredicatePrecisionAdjustment implements PrecisionAdjustment {

  // statistics
  final Timer totalPrecTime = new Timer();
  final Timer computingAbstractionTime = new Timer();

  public static int numAbstractions = 0;
  int numAbstractionsFalse = 0;
  int maxBlockSize = 0;

  private final LogManager logger;
  private final PredicateAbstractionManager formulaManager;
  private final PathFormulaManager pathFormulaManager;
  private final FormulaManagerView fmgr;

  private final Solver solver;
  private @Nullable InvariantGenerator invariantGenerator;
  private InvariantSupplier invariants;

  public PredicatePrecisionAdjustment(PredicateCPA pCpa,
      InvariantGenerator pInvariantGenerator) {

    logger = pCpa.getLogger();
    formulaManager = pCpa.getPredicateManager();
    pathFormulaManager = pCpa.getPathFormulaManager();
    fmgr = pCpa.getSolver().getFormulaManager();

    solver = pCpa.getSolver();

    invariantGenerator = checkNotNull(pInvariantGenerator);
    invariants = InvariantSupplier.TrivialInvariantSupplier.INSTANCE;
  }

  @Override
  public Optional<PrecisionAdjustmentResult> prec(
      AbstractState pElement,
      Precision pPrecision,
      UnmodifiableReachedSet pElements,
      Function<AbstractState, AbstractState> projection,
      AbstractState fullState) throws CPAException, InterruptedException {

    totalPrecTime.start();
    try {
      PredicateAbstractState element = (PredicateAbstractState)pElement;

      if (element instanceof ComputeAbstractionState) {
        PredicatePrecision precision = (PredicatePrecision)pPrecision;



        if(IncrementalPAUtil.isInit && CPAMain.isIncPred) {
          ImpactedHelper.trys++;
          return computeAbstraction((ComputeAbstractionState) element, precision);
        }
        else
          return computeAbstraction1((ComputeAbstractionState)element, precision);
      } else {
        return Optional.of(PrecisionAdjustmentResult.create(
            element, pPrecision, PrecisionAdjustmentResult.Action.CONTINUE));
      }


    } finally {
      totalPrecTime.stop();
    }
  }

  /**
   * Compute an abstraction.
   */
  private Optional<PrecisionAdjustmentResult> computeAbstraction(
      ComputeAbstractionState element,
      PredicatePrecision precision) throws CPAException, InterruptedException {

    AbstractionFormula abstractionFormula = element.getAbstractionFormula();
    PersistentMap<CFANode, Integer> abstractionLocations = element.getAbstractionLocationsOnPath();
    PathFormula pathFormula = element.getPathFormula();
    CFANode loc = element.getLocation();
    Integer newLocInstance = firstNonNull(abstractionLocations.get(loc), 0) + 1;
    Collection<AbstractionPredicate> addedPredicates = new HashSet<>();

    AbstractionFormula newAbstractionFormula = null;

    int actualLoc = loc.getNodeNumber();
//    if(loc instanceof CFunctionEntryNode && !loc.getFunctionName().equals(CPAMain.entryFunction)) {
//      actualLoc = IncrementalPAUtil.getInstance().prevLoc;
//    }

    Map<Integer, Pair> lastVFileDisjInvariants =
        ImpactedHelper.getInstance().lastVFileDisjInvariants;
    Pair<PredicatePrecision, AbstractionFormula> storedInvariant = lastVFileDisjInvariants.get(actualLoc);

    if(storedInvariant == null) {
      if(lastVFileDisjInvariants.containsKey(actualLoc - 1))
        storedInvariant = lastVFileDisjInvariants.get(actualLoc - 1);

      if(storedInvariant == null && lastVFileDisjInvariants.containsKey(actualLoc + 1))
        storedInvariant = lastVFileDisjInvariants.get(actualLoc + 1);
      // System.out.println("Imprecise hit");
    }
    try {
      Set<AbstractionPredicate> preds;

      if(ImpactedHelper.getInstance().isFunctionWide) {
        preds = precision.getFunctionPredicates().get(loc.getFunctionName());
      } else {
        preds = precision.getPredicates(loc, newLocInstance);
      }
      if (storedInvariant != null) {
        boolean isImpacted =
            ImpactedHelper.getInstance().checkImpacted(storedInvariant.getSecond());

        if (!isImpacted) {
          ImpactedHelper.isHit = true;
          ImpactedHelper.hits++;
          Region r = GlobalInfo.getInstance().getAbstractionManager().buildRegionFromFormula(storedInvariant.getSecond().asFormula());
          BooleanFormula newInstantiatedFormula = fmgr.instantiate(storedInvariant.getSecond().asFormula(), pathFormula.getSsa().withDefault(1));
          addedPredicates.addAll(GlobalInfo.getInstance().predicateManager.extractPredicates(newInstantiatedFormula));
          if(GlobalInfo.getInstance().predicateSharing == PredicateSharing.FUNCTION) {
            Multimap<String, AbstractionPredicate> newFuncPredicates = ArrayListMultimap.create();
            newFuncPredicates.putAll(loc.getFunctionName(), addedPredicates);
            precision = precision.addFunctionPredicates(newFuncPredicates);
            ImpactedHelper.getInstance().bestPrecisionPerFunction =
                ImpactedHelper.getInstance().bestPrecisionPerFunction
                    .addFunctionPredicates(newFuncPredicates);

            precision = precision.addGlobalPredicates(addedPredicates);
            ImpactedHelper.getInstance().bestPrecisionPerFunction =
                ImpactedHelper.getInstance().bestPrecisionPerFunction
                    .addGlobalPredicates(addedPredicates);
          } else if (GlobalInfo.getInstance().predicateSharing == PredicateSharing.GLOBAL) {
            precision = precision.addGlobalPredicates(addedPredicates);
            ImpactedHelper.getInstance().bestPrecisionPerFunction =
                ImpactedHelper.getInstance().bestPrecisionPerFunction
                    .addGlobalPredicates(addedPredicates);
          }
//          newAbstractionFormula = new AbstractionFormula(fmgr, r, storedInvariant.getSecond().asFormula(), newInstantiatedFormula, pathFormulaManager.makeEmptyPathFormula(pathFormula),  storedInvariant.getSecond().getIdsOfStoredAbstractionReused());

          newAbstractionFormula = new AbstractionFormula(fmgr, r, storedInvariant.getSecond().asFormula(), newInstantiatedFormula, pathFormula,  storedInvariant.getSecond().getIdsOfStoredAbstractionReused());

          ImpactedHelper.getInstance().lastVFileDisjInvariants.remove(actualLoc);


          BooleanFormula tmp_instantiatedFormula =
              newAbstractionFormula.asInstantiatedFormula();
          preds = new HashSet<>(
              GlobalInfo.getInstance().predicateManager.extractPredicates(tmp_instantiatedFormula));

          AbstractionFormula tmp =
              formulaManager.buildAbstraction(loc, abstractionFormula, pathFormula, preds);
          boolean valid = formulaManager.checkCoverage(tmp,
              newAbstractionFormula);
          if(!valid) {
            newAbstractionFormula = makeFalseAbstractionState(pathFormula);
            // System.out.println("not valid!!");
            ImpactedHelper.nonvalids ++;
          }
        } else {
          AbstractionFormula absF = null;
          BooleanFormula formula = null;
          if(ImpactedHelper.getInstance().isEliminate) {
              absF = checkNotNull(storedInvariant.getSecond());
              formula = absF.asFormula();
          }

          //TODO qianshan eliminate the impacted predicates
          if (ImpactedHelper.getInstance().isEliminate) {
            Pair<Boolean, BooleanFormula> wF = ImpactedHelper.getInstance().eliminate(formula);
            BooleanFormula wFormula = wF.getSecond();

            BooleanFormula wInstantiatedFormula = null;
            if(wFormula != null)
              wInstantiatedFormula = fmgr.instantiate(wFormula,
                  pathFormula.getSsa().withDefault(1));


            boolean validElimination = wFormula != null;
            boolean isChanged = wF.getFirst();
            boolean valid = false;
            boolean isBot;
            try{
              isBot =
                  GlobalInfo.getInstance().getSmtInterpolBooleanFormulaManager().isFalse(wFormula);
            } catch (NullPointerException npe) {
              isBot = true;
            }

            if(isChanged && !isBot){
//              newAbstractionFormula =
//                  new AbstractionFormula(GlobalInfo.getInstance().getFormulaManagerView(),
//                      absF.asRegion(), wFormula,
//                      wInstantiatedFormula, pathFormulaManager.makeEmptyPathFormula(pathFormula), ImmutableSet.<Integer>of());
              newAbstractionFormula =
                  new AbstractionFormula(GlobalInfo.getInstance().getFormulaManagerView(),
                      absF.asRegion(), wFormula,
                      wInstantiatedFormula, pathFormula, ImmutableSet.<Integer>of());
              System.out.println("validation check");
              BooleanFormula tmp_instantiatedFormula =
                  newAbstractionFormula.asInstantiatedFormula();
              preds = new HashSet<>(
                  GlobalInfo.getInstance().predicateManager.extractPredicates(tmp_instantiatedFormula));
              AbstractionFormula tmp =
                  formulaManager.buildAbstraction(loc, abstractionFormula, pathFormula, preds);
              valid = formulaManager.checkCoverage(tmp,
                  newAbstractionFormula);
              if(!valid) {
                ImpactedHelper.nonvalids++;
              }
            }
            if(ImpactedHelper.getInstance().isEliminate && validElimination && valid) {
              addedPredicates.addAll(GlobalInfo.getInstance().predicateManager.extractPredicates(wInstantiatedFormula));
              if(GlobalInfo.getInstance().predicateSharing == PredicateSharing.FUNCTION) {
                Multimap<String, AbstractionPredicate> newFuncPredicates = ArrayListMultimap.create();
                newFuncPredicates.putAll(loc.getFunctionName(), addedPredicates);
                precision = precision.addFunctionPredicates(newFuncPredicates);
                ImpactedHelper.getInstance().bestPrecisionPerFunction =
                    ImpactedHelper.getInstance().bestPrecisionPerFunction
                        .addFunctionPredicates(newFuncPredicates);

                precision = precision.addGlobalPredicates(addedPredicates);
                ImpactedHelper.getInstance().bestPrecisionPerFunction =
                    ImpactedHelper.getInstance().bestPrecisionPerFunction
                        .addGlobalPredicates(addedPredicates);
              } else if (GlobalInfo.getInstance().predicateSharing == PredicateSharing.GLOBAL) {
                precision = precision.addGlobalPredicates(addedPredicates);
                ImpactedHelper.getInstance().bestPrecisionPerFunction =
                    ImpactedHelper.getInstance().bestPrecisionPerFunction
                        .addGlobalPredicates(addedPredicates);
              }

//              newAbstractionFormula =
//                  new AbstractionFormula(GlobalInfo.getInstance().getFormulaManagerView(),
//                      absF.asRegion(), wFormula,
//                      wInstantiatedFormula, pathFormulaManager.makeEmptyPathFormula(pathFormula), ImmutableSet.<Integer>of());
              ImpactedHelper.isHit = true;
              ImpactedHelper.partialHits++;
              // newAbstractionFormula = makeFalseAbstractionState(pathFormula);
            } else {
              // yqs17: compute the abstraction from scrach
              newAbstractionFormula = makeFalseAbstractionState(pathFormula);
//              newAbstractionFormula =
//                  formulaManager.buildAbstraction(loc, abstractionFormula, pathFormula, preds);
            }
          }

          // compute a new abstraction with a precision based on `preds`
//          if(!ImpactedHelper.getInstance().isEliminate) {
//            newAbstractionFormula =
//                formulaManager.buildAbstraction(loc, abstractionFormula, pathFormula, preds);
//          }
        }
        ImpactedHelper.getInstance().curImpactedVariables.clear();
      } else {
        newAbstractionFormula = makeFalseAbstractionState(pathFormula);
      }
    } catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
    // if the abstraction is false, return bottom (represented by empty set)
    assert newAbstractionFormula != null;
    if (newAbstractionFormula.isFalse()) {
      ImpactedHelper.bots ++;
      // yqs17: \bot处断开，不往后重用annotation
      //if(!CPAMain.isIncPred)
      return Optional.absent();
    } else {
      BooleanFormula instantiatedFormula =
          newAbstractionFormula.asInstantiatedFormula();
      if(!instantiatedFormula.toString().equals("true")) {
        if(!ImpactedHelper.getInstance().extractInitialPrec) {
          addedPredicates.addAll(GlobalInfo.getInstance().predicateManager
              .extractPredicates(instantiatedFormula));
          Multimap<String, AbstractionPredicate> newFuncPredicates =
              ArrayListMultimap.create();
          newFuncPredicates
              .putAll(loc.getFunctionName(), addedPredicates);
          GlobalInfo.getInstance().predicateCPA.initialPrecision =
              GlobalInfo.getInstance().predicateCPA.initialPrecision
                  .addFunctionPredicates(newFuncPredicates);
          GlobalInfo.getInstance().predicateCPA.initialPrecision =
              GlobalInfo.getInstance().predicateCPA.initialPrecision
                  .addGlobalPredicates(addedPredicates);
        }
      }
    }

    PathFormula newPathFormula;
    if(ImpactedHelper.isHit && ImpactedHelper.getInstance().isInvDisj) {
      if(!ImpactedHelper.getInstance().aggressive_pathformula) {
        newPathFormula = pathFormulaManager.makeEmptyPathFormula(pathFormula);
        //newPathFormula = GlobalInfo.getInstance().getEmptyPathFormula();
      } else {
        newPathFormula = newAbstractionFormula.getBlockFormula();
      }
      ImpactedHelper.isHit = false;
    } else {
      // create new empty path formula
      newPathFormula = pathFormulaManager.makeEmptyPathFormula(pathFormula);
    }

    // update abstraction locations map
    abstractionLocations = abstractionLocations.putAndCopy(loc, newLocInstance);

    PredicateAbstractState state =
        PredicateAbstractState.mkAbstractionState(newPathFormula,
            newAbstractionFormula, abstractionLocations);
    return Optional.of(PrecisionAdjustmentResult.create(
        state, precision, PrecisionAdjustmentResult.Action.CONTINUE));
  }

  private Optional<PrecisionAdjustmentResult> computeAbstraction1(
      ComputeAbstractionState element,
      PredicatePrecision precision) throws CPAException, InterruptedException{
    AbstractionFormula abstractionFormula = element.getAbstractionFormula();
    PersistentMap<CFANode, Integer> abstractionLocations = element.getAbstractionLocationsOnPath();
    PathFormula pathFormula = element.getPathFormula();
    CFANode loc = element.getLocation();
    Integer newLocInstance = firstNonNull(abstractionLocations.get(loc), 0) + 1;

    numAbstractions++;
    logger.log(Level.FINEST, "Computing abstraction at instance", newLocInstance, "of node", loc, "in path.");

    maxBlockSize = Math.max(maxBlockSize, pathFormula.getLength());

    // get invariants and add them
    extractInvariants();
    BooleanFormula invariant = invariants.getInvariantFor(loc, fmgr, pathFormulaManager);
    if (invariant != null) {
      pathFormula = pathFormulaManager.makeAnd(pathFormula, invariant);
    }

    AbstractionFormula newAbstractionFormula = null;

    // compute new abstraction
    computingAbstractionTime.start();
    try {
      Set<AbstractionPredicate> preds;

      if(CPAMain.isIncPred && CEGARStatistics.countRefinements == 0) {
        preds = precision.getFunctionPredicates().get(loc.getFunctionName());
      } else
        preds = precision.getPredicates(loc, newLocInstance);

      if(precision.getGlobalPredicates().size() != 0 && preds.size() == 0) {
        preds = precision.getGlobalPredicates();
      }

      boolean isUnsat = false;
      if(preds.size() == 0 && CPAMain.isIncPred) {
      // if(false) {
        BooleanFormula testF =
            fmgr.makeAnd(pathFormula.getFormula(),
                abstractionFormula.asInstantiatedFormula());
        isUnsat = solver.isUnsat(testF);
        // System.out.println("Checking unsat..." + isUnsat);
      }
      if(isUnsat) {
        numAbstractionsFalse++;
        logger.log(Level.FINEST, "Abstraction is false, node is not reachable");
        return Optional.absent();
      } else {
        // compute a new abstraction with a precision based on `preds`
        newAbstractionFormula = formulaManager.buildAbstraction(
            loc, abstractionFormula, pathFormula, preds);
      }
    } finally {
      computingAbstractionTime.stop();
    }

    // if the abstraction is false, return bottom (represented by empty set)
    if (newAbstractionFormula.isFalse()) {
      numAbstractionsFalse++;
      logger.log(Level.FINEST, "Abstraction is false, node is not reachable");
      return Optional.absent();
    }

    // create new empty path formula
    PathFormula newPathFormula = pathFormulaManager.makeEmptyPathFormula(pathFormula);

    // initialize path formula with current invariants
    if (invariant != null) {
      newPathFormula = pathFormulaManager.makeAnd(newPathFormula, invariant);
    }

    // update abstraction locations map
    abstractionLocations = abstractionLocations.putAndCopy(loc, newLocInstance);

    PredicateAbstractState state =
        PredicateAbstractState.mkAbstractionState(newPathFormula,
            newAbstractionFormula, abstractionLocations);
    return Optional.of(PrecisionAdjustmentResult.create(
        state, precision, PrecisionAdjustmentResult.Action.CONTINUE));

  }


  private AbstractionFormula makeFalseAbstractionState(PathFormula pathFormula) {
    BooleanFormula botFormula =
        ImpactedHelper.getInstance().bmgr.makeBoolean(false);
//    BooleanFormula botFormula =
//        ImpactedHelper.getInstance().bmgr.makeBoolean(true);
    IncrementalPAUtil.getInstance().numOfBot++;
    IncrementalPAUtil.getInstance().isInvMiss = true;
    return
        new AbstractionFormula(GlobalInfo.getInstance().getFormulaManagerView(),
            GlobalInfo.getInstance().getRegionManager().makeFalse(), botFormula,
            botFormula, pathFormulaManager.makeEmptyPathFormula(pathFormula), ImmutableSet.<Integer>of());
  }

  private void extractInvariants() throws CPAException {
    if (invariantGenerator == null) {
      return; // already done
    }

    try {
      invariants = invariantGenerator.get();

    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();

    } finally {
      invariantGenerator = null; // to allow GC'ing it and the ReachedSet
    }
  }

  void setInitialLocation(CFANode initialLocation) {
    if(invariantGenerator == null) {
      invariantGenerator = ImpactedHelper.getInstance().invariantGenerator;
    }
    invariantGenerator.start(initialLocation);
    ImpactedHelper.getInstance().invariantGenerator = invariantGenerator;
  }
}
