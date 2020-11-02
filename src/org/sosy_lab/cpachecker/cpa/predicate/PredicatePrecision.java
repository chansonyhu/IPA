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

import com.google.common.base.Supplier;
import com.google.common.collect.MultimapBuilder.SetMultimapBuilder;
import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import com.google.common.collect.*;
import java.util.TreeSet;
import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.UniqueIdGenerator;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;

import com.google.common.base.Function;
import com.google.common.base.Functions;

import static com.google.common.base.Preconditions.checkArgument;

/**
 * This class represents the precision of the PredicateCPA.
 * It is basically a map which assigns to each node in the CFA a (possibly empty)
 * set of predicates which should be used at this location.
 * Additionally, there may be some predicates which are used for all locations
 * ("global" predicates), and some predicates which are used for all locations
 * within a specific function.
 *
 * All instances of this class are immutable.
 */
public class PredicatePrecision implements Precision, Serializable {

  private static final long serialVersionUID = 6756384228231447937L;
  // do not access theses sets directly except in their getters
  // (overrides from subclass need to be used)
  public SetMultimap<Pair<Integer, Integer>, AbstractionPredicate> mLocationInstancePredicates;
  public SetMultimap<Integer, AbstractionPredicate> mLocalPredicates;
  public SetMultimap<String, AbstractionPredicate> mFunctionPredicates;
  public Set<AbstractionPredicate> mGlobalPredicates;

  private boolean deserializerFlag = false;

  private static final UniqueIdGenerator idGenerator = new UniqueIdGenerator();
  private final int id = idGenerator.getFreshId();

  public PredicatePrecision() {
    deserializerFlag = true;
  }

  public PredicatePrecision(
      Multimap<Pair<CFANode, Integer>, AbstractionPredicate> pLocationInstancePredicates,
      Multimap<CFANode, AbstractionPredicate> pLocalPredicates,
      Multimap<String, AbstractionPredicate> pFunctionPredicates,
      Collection<AbstractionPredicate> pGlobalPredicates) {
    Multimap<Pair<Integer, Integer>, AbstractionPredicate> curLocationInstancePredicates
            = HashMultimap.create();
    for(Pair<CFANode, Integer> key : pLocationInstancePredicates.keySet()) {
      Pair<Integer, Integer> simKey = Pair.of(key.getFirst().getNodeNumber(), key.getSecond());
      curLocationInstancePredicates.putAll(simKey, pLocationInstancePredicates.get(key));
    }
    Multimap<Integer, AbstractionPredicate> curLocalPredicates
            = HashMultimap.create();
    for(CFANode key : pLocalPredicates.keySet()) {
      Integer simKey = key.getNodeNumber();
      curLocalPredicates.putAll(simKey, pLocalPredicates.get(key));
    }
    //mLocationInstancePredicates = ImmutableSetMultimap.copyOf(curLocationInstancePredicates);
    Map<String, Collection<AbstractionPredicate>> tmpLocationInstancePredicates = Maps.newHashMap();
    mLocationInstancePredicates =  Multimaps.newSetMultimap(tmpLocationInstancePredicates, new SetSupplier());
    mLocationInstancePredicates.putAll(curLocationInstancePredicates);

    //mLocalPredicates = sortedImmutableSetCopyOf(curLocalPredicates);
    Map<String, Collection<AbstractionPredicate>> tmpLocalPredicates = Maps.newHashMap();
    mLocalPredicates =  Multimaps.newSetMultimap(tmpLocalPredicates, new SetSupplier());
    mLocalPredicates.putAll(curLocalPredicates);

    //mFunctionPredicates = sortedImmutableSetCopyOf(pFunctionPredicates);
    Map<String, Collection<AbstractionPredicate>> tmpFunctionPredicates = Maps.newHashMap();
    mFunctionPredicates =  Multimaps.newSetMultimap(tmpFunctionPredicates, new SetSupplier());
    mFunctionPredicates.putAll(pFunctionPredicates);

    mGlobalPredicates = ImmutableSet.copyOf(pGlobalPredicates);
  }

  private static <K extends Comparable<? super K>, V>
      ImmutableSetMultimap<K, V> sortedImmutableSetCopyOf(Multimap<K, V> m) {
    return ImmutableSetMultimap
        .<K, V>builder()
        .orderKeysBy(Ordering.natural())
        .putAll(m)
        .build();
  }

  private static class SortedSetSupplier extends CountingSupplier<TreeSet<AbstractionPredicate>> {
    @Override
    public TreeSet<AbstractionPredicate> getImpl() {
      return Sets.newTreeSet(Ordering.allEqual());
    }

    private static final long serialVersionUID = 0;
  }

  private static class SetSupplier<T> extends CountingSupplier<Set<T>> {
    @Override
    public Set<T> getImpl() {
      return new HashSet<>(4);
    }

    private static final long serialVersionUID = 0;
  }

  private abstract static class CountingSupplier<E> implements Supplier<E>, Serializable {
    int count;

    abstract E getImpl();

    @Override
    public E get() {
      count++;
      return getImpl();
    }
  }
  /**
   * Create a new, empty precision.
   */
  public static PredicatePrecision empty() {
    return new PredicatePrecision(
        ImmutableSetMultimap.<Pair<CFANode, Integer>, AbstractionPredicate>of(),
        ImmutableSetMultimap.<CFANode, AbstractionPredicate>of(),
        ImmutableSetMultimap.<String, AbstractionPredicate>of(),
        ImmutableSet.<AbstractionPredicate>of());
  }

  /**
   * Return a table of the location-instance-specific predicates.
   * These are the predicates that should be used at the n-th instance
   * of an abstraction location l in the current path.
   */
  public ImmutableSetMultimap<Pair<CFANode, Integer>, AbstractionPredicate> getLocationInstancePredicates() {
    Multimap<Pair<CFANode, Integer>, AbstractionPredicate> realLocationInstancePredicates
            = HashMultimap.create();
    for(Pair<Integer, Integer> simKey : mLocationInstancePredicates.keySet()) {
      CFANode node = GlobalInfo.getInstance().getCFAInfo().get().getNodeByNodeNumber(simKey.getFirst());
      Pair<CFANode, Integer> key = Pair.of(node, simKey.getSecond());
      realLocationInstancePredicates.putAll(key, mLocationInstancePredicates.get(simKey));
    }
    return ImmutableSetMultimap.copyOf(realLocationInstancePredicates);
    //return mLocationInstancePredicates;
  }

  /**
   * Return a map view of the location-specific predicates of this precision.
   */
  public ImmutableSetMultimap<CFANode, AbstractionPredicate> getLocalPredicates() {
    Multimap<CFANode, AbstractionPredicate> realLocalPredicates
            = HashMultimap.create();
    for(Integer simKey : mLocalPredicates.keySet()) {
      CFANode node = GlobalInfo.getInstance().getCFAInfo().get().getNodeByNodeNumber(simKey);
      if(node == null)
        continue;
      realLocalPredicates.putAll(node, mLocalPredicates.get(simKey));
    }
    return ImmutableSetMultimap.copyOf(realLocalPredicates);
    //return mLocalPredicates;
  }

  /**
   * Return a map view of the function-specific predicates of this precision.
   */
  public SetMultimap<String, AbstractionPredicate> getFunctionPredicates() {
    return mFunctionPredicates;
  }

  /**
   * Return all global predicates in this precision.
   */
  public Set<AbstractionPredicate> getGlobalPredicates() {
    return mGlobalPredicates;
  }

  /**
   * Return all predicates for one specific location in this precision.
   * @param loc A CFA location.
   * @param locInstance How often this location has appeared in the current path.
   */
  public Set<AbstractionPredicate> getPredicates(CFANode loc, Integer locInstance) {
    Set<AbstractionPredicate> result = getLocationInstancePredicates().get(Pair.of(loc, locInstance));
    if (result.isEmpty()) {
      result = getLocalPredicates().get(loc);
    }
    if (result.isEmpty()) {
      result = getFunctionPredicates().get(loc.getFunctionName());
    }
    if (result.isEmpty()) {
      result = getGlobalPredicates();
    }
    return result;
  }

  /**
   * Create a new precision which is a copy of the current one with some
   * additional global predicates.
   */
  public PredicatePrecision addGlobalPredicates(Collection<AbstractionPredicate> newPredicates) {
    List<AbstractionPredicate> predicates = Lists.newArrayList(getGlobalPredicates());
    predicates.addAll(newPredicates);
    return new PredicatePrecision(getLocationInstancePredicates(),
        getLocalPredicates(), getFunctionPredicates(), predicates);
  }

  /**
   * Create a new precision which is a copy of the current one with some
   * additional function-specific predicates.
   */
  public PredicatePrecision addFunctionPredicates(Multimap<String, AbstractionPredicate> newPredicates) {
    Multimap<String, AbstractionPredicate> predicates = ArrayListMultimap.create(getFunctionPredicates());
    predicates.putAll(newPredicates);

    // During lookup, we do not look into getGlobalPredicates(),
    // if there is something for the key in predicates.
    // Thus, we copy the relevant items into the predicates set here.
    if (!getGlobalPredicates().isEmpty()) {
      for (String function : newPredicates.keySet()) {
        predicates.putAll(function, getGlobalPredicates());
      }
    }

    return new PredicatePrecision(getLocationInstancePredicates(),
        getLocalPredicates(), predicates, getGlobalPredicates());
  }

  /**
   * Create a new precision which is a copy of the current one with some
   * additional location-specific predicates.
   */
  public PredicatePrecision addLocalPredicates(Multimap<CFANode, AbstractionPredicate> newPredicates) {
    Multimap<CFANode, AbstractionPredicate> predicates = ArrayListMultimap.create(getLocalPredicates());
    predicates.putAll(newPredicates);

    // During lookup, we do not look into getGlobalPredicates() and getFunctionPredicates(),
    // if there is something for the key in predicates.
    // Thus, we copy the relevant items into the predicates set here.
    if (!getGlobalPredicates().isEmpty() || !getFunctionPredicates().isEmpty()) {
      for (CFANode newLoc : newPredicates.keySet()) {
        predicates.putAll(newLoc, getFunctionPredicates().get(newLoc.getFunctionName()));
        predicates.putAll(newLoc, getGlobalPredicates());
      }
    }

    return new PredicatePrecision(getLocationInstancePredicates(),
        predicates, getFunctionPredicates(), getGlobalPredicates());
  }

  /**
   * Create a new precision which is a copy of the current one with some
   * additional location-specific predicates.
   */
  public PredicatePrecision addLocalPredicates1(ImmutableMultimap<CFANode, AbstractionPredicate> newPredicates) {
    Multimap<CFANode, AbstractionPredicate> predicates = ArrayListMultimap.create(getLocalPredicates());
    predicates.putAll(newPredicates);

    // During lookup, we do not look into getGlobalPredicates() and getFunctionPredicates(),
    // if there is something for the key in predicates.
    // Thus, we copy the relevant items into the predicates set here.
    if (!getGlobalPredicates().isEmpty() || !getFunctionPredicates().isEmpty()) {
      for (CFANode newLoc : newPredicates.keySet()) {
        predicates.putAll(newLoc, getFunctionPredicates().get(newLoc.getFunctionName()));
        predicates.putAll(newLoc, getGlobalPredicates());
      }
    }

    return new PredicatePrecision(getLocationInstancePredicates(),
        predicates, getFunctionPredicates(), getGlobalPredicates());
  }

  /**
   * Create a new precision which is a copy of the current one with some
   * additional location-instance-specific predicates.
   */
  public PredicatePrecision addLocationInstancePredicates(
      Multimap<Pair<CFANode, Integer>, AbstractionPredicate> newPredicates) {
    Multimap<Pair<CFANode, Integer>, AbstractionPredicate> predicates = ArrayListMultimap.create(getLocationInstancePredicates());
    predicates.putAll(newPredicates);

    // During lookup, we do not look into getGlobalPredicates(),
    // getFunctionPredicates(), and getLocalPredicates(),
    // if there is something for the key in predicates.
    // Thus, we copy the relevant items into the predicates set here.
    if (!getGlobalPredicates().isEmpty() || !getFunctionPredicates().isEmpty() || !getLocalPredicates().isEmpty()) {
      for (Pair<CFANode, Integer> key : newPredicates.keySet()) {
        CFANode loc = key.getFirst();
        predicates.putAll(key, getLocalPredicates().get(loc));
        predicates.putAll(key, getFunctionPredicates().get(loc.getFunctionName()));
        predicates.putAll(key, getGlobalPredicates());
      }
    }

    return new PredicatePrecision(predicates, getLocalPredicates(),
        getFunctionPredicates(), getGlobalPredicates());
  }

  /**
   * Create a new precision which contains all predicates of this precision
   * and a second one.
   */
  public PredicatePrecision mergeWith(PredicatePrecision prec) {
    // create new set of global predicates
    Collection<AbstractionPredicate> newGlobalPredicates = Lists.newArrayList(getGlobalPredicates());
    newGlobalPredicates.addAll(prec.getGlobalPredicates());
    newGlobalPredicates = ImmutableSet.copyOf(newGlobalPredicates);

    // create new multimap of function-specific predicates
    Multimap<String, AbstractionPredicate> newFunctionPredicates = ArrayListMultimap.create(getFunctionPredicates());
    newFunctionPredicates.putAll(prec.getFunctionPredicates());

    if (!newGlobalPredicates.isEmpty()) {
      for (String function : newFunctionPredicates.keySet()) {
        newFunctionPredicates.putAll(function, newGlobalPredicates);
      }
    }
    newFunctionPredicates = ImmutableSetMultimap.copyOf(newFunctionPredicates);

    // create new multimap of location-specific predicates
    Multimap<CFANode, AbstractionPredicate> newLocalPredicates = ArrayListMultimap.create(getLocalPredicates());
    newLocalPredicates.putAll(prec.getLocalPredicates());

    if (!newGlobalPredicates.isEmpty() || !newFunctionPredicates.isEmpty()) {
      for (CFANode loc : newLocalPredicates.keySet()) {
        newLocalPredicates.putAll(loc, newGlobalPredicates);
        newLocalPredicates.putAll(loc, newFunctionPredicates.get(loc.getFunctionName()));
      }
    }

    // create new multimap of location-instance-specific predicates
    Multimap<Pair<CFANode, Integer>, AbstractionPredicate> newLocationInstanceSpecificPredicates = ArrayListMultimap.create(getLocationInstancePredicates());
    newLocationInstanceSpecificPredicates.putAll(prec.getLocationInstancePredicates());

    if (!newGlobalPredicates.isEmpty() || !newFunctionPredicates.isEmpty() || !newLocalPredicates.isEmpty()) {
      for (Pair<CFANode, Integer> key : newLocationInstanceSpecificPredicates.keySet()) {
        newLocationInstanceSpecificPredicates.putAll(key, newGlobalPredicates);
        newLocationInstanceSpecificPredicates.putAll(key, newFunctionPredicates.get(key.getFirst().getFunctionName()));
        newLocationInstanceSpecificPredicates.putAll(key, newLocalPredicates.get(key.getFirst()));
      }
    }

    return new PredicatePrecision(newLocationInstanceSpecificPredicates,
        newLocalPredicates, newFunctionPredicates, newGlobalPredicates);
  }

  /**
   * Calculates a "difference" from this precision to another precision.
   * The difference is the number of predicates which are present in this precision,
   * and are missing in the other precision.
   * If a predicate is present in both precisions, but for different locations,
   * this counts as a difference.
   *
   * Note that this difference is not symmetric!
   * (Similar to {@link Sets#difference(Set, Set)}).
   */
  public int calculateDifferenceTo(PredicatePrecision other) {
    int difference = 0;
    difference += Sets.difference(this.getGlobalPredicates(),
                                  other.getGlobalPredicates()).size();

    difference += Sets.difference(this.getFunctionPredicates().entries(),
                                  other.getFunctionPredicates().entries()).size();

    difference += Sets.difference(this.getLocalPredicates().entries(),
                                  other.getLocalPredicates().entries()).size();

    difference += Sets.difference(this.getLocationInstancePredicates().entries(),
                                  other.getLocationInstancePredicates().entries()).size();
    return difference;
  }

  @Override
  public int hashCode() {
    checkArgument(getFunctionPredicates() != null);
    return Objects.hash(getGlobalPredicates(),
                             getFunctionPredicates(),
                             getLocalPredicates(),
                             getLocationInstancePredicates());
  }

  @Override
  public boolean equals(Object pObj) {
    if (pObj == this) {
      return true;
    } else if (pObj == null) {
      return false;
    } else if (!(pObj.getClass().equals(this.getClass()))) {
      return false;
    } else {
      PredicatePrecision other = (PredicatePrecision)pObj;
      return getLocationInstancePredicates().equals(other.getLocationInstancePredicates())
          && getLocalPredicates().equals(other.getLocalPredicates())
          && getFunctionPredicates().equals(other.getFunctionPredicates())
          && getGlobalPredicates().equals(other.getGlobalPredicates());
    }
  }

  @Override
  public String toString() {
    if(deserializerFlag)
      return "";
    if(getGlobalPredicates() == null) {
      return "";
    }
    StringBuilder sb = new StringBuilder();
    if (!getGlobalPredicates().isEmpty())  {
      sb.append("global predicates: ");
      sb.append(getGlobalPredicates());
    }
    if (!getFunctionPredicates().isEmpty()) {
      if (sb.length() > 0) {
        sb.append(", ");
      }
      sb.append("function predicates: ");
      sb.append(getFunctionPredicates());
    }
    if (!getLocalPredicates().isEmpty()) {
      if (sb.length() > 0) {
        sb.append(", ");
      }
      sb.append("local predicates: ");
      sb.append(getLocalPredicates());
    }
    if (!getLocationInstancePredicates().isEmpty()) {
      if (sb.length() > 0) {
        sb.append(", ");
      }
      sb.append("location-instance predicates: ");
      sb.append(getLocationInstancePredicates());
    }

    if (sb.length() == 0) {
      return "empty";
    } else {
      return sb.toString();
    }
  }

  /**
   * Get the unique id of this precision object.
   */
  public int getId() {
    return id;
  }

  static ListMultimap<String, AbstractionPredicate> mergePredicatesPerFunction(
      Multimap<Pair<CFANode, Integer>, AbstractionPredicate> newPredicates) {

    return transformAndMergeKeys(newPredicates,
        Functions.compose(CFAUtils.GET_FUNCTION,
                          Pair.<CFANode>getProjectionToFirst()));
  }

  static ListMultimap<CFANode, AbstractionPredicate> mergePredicatesPerLocation(
      Multimap<Pair<CFANode, Integer>, AbstractionPredicate> newPredicates) {

    return transformAndMergeKeys(newPredicates, Pair.<CFANode>getProjectionToFirst());
  }

  private static <K1, K2, V> ListMultimap<K2, V> transformAndMergeKeys(Multimap<K1, V> input,
      Function<? super K1, K2> transformFunction) {

    ListMultimap<K2, V> result = ArrayListMultimap.create();
    for (Map.Entry<K1, Collection<V>> entry : input.asMap().entrySet()) {
      result.putAll(transformFunction.apply(entry.getKey()), entry.getValue());
    }
    return result;
  }
}