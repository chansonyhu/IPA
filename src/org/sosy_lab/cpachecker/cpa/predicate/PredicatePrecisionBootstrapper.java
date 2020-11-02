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

import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.logging.Level;

import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.core.interfaces.Statistics;
import org.sosy_lab.cpachecker.core.interfaces.StatisticsProvider;
import org.sosy_lab.cpachecker.cpa.predicate.persistence.PredicateMapParser;
import org.sosy_lab.cpachecker.cpa.predicate.persistence.PredicatePersistenceUtils.PredicateParsingFailedException;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.AbstractionPredicate;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.statistics.AbstractStatistics;

import com.google.common.collect.ImmutableList;

@Options(prefix="cpa.predicate")
public class PredicatePrecisionBootstrapper implements StatisticsProvider {

  @Option(secure=true, name="abstraction.initialPredicates",
      description="get an initial map of predicates from a list of files (see source doc/examples/predmap.txt for an example)")
  @FileOption(FileOption.Type.OPTIONAL_INPUT_FILE)
  private List<Path> predicatesFiles = ImmutableList.of();

  private Timer readPrecisionTimer = new Timer();

  @Option(secure=true, description="always check satisfiability at end of block, even if precision is empty")
  private boolean checkBlockFeasibility = false;

  private final FormulaManagerView formulaManagerView;
  private final AbstractionManager abstractionManager;

  private final Configuration config;
  private final LogManager logger;
  private final CFA cfa;

  private static class PrecisionBootstrapStatistics extends AbstractStatistics {}
  private final PrecisionBootstrapStatistics statistics = new PrecisionBootstrapStatistics();

  public PredicatePrecisionBootstrapper(Configuration config, LogManager logger, CFA cfa,
      PathFormulaManager pathFormulaManager, AbstractionManager abstractionManager, FormulaManagerView formulaManagerView) throws InvalidConfigurationException {
    this.config = config;
    this.logger = logger;
    this.cfa = cfa;

    this.abstractionManager = abstractionManager;
    this.formulaManagerView = formulaManagerView;

    config.inject(this);
  }

  private PredicatePrecision internalPrepareInitialPredicates() throws InvalidConfigurationException {

    PredicatePrecision result = PredicatePrecision.empty();

    if (checkBlockFeasibility) {
      result = result.addGlobalPredicates(Collections.<AbstractionPredicate>singleton(abstractionManager.makeFalsePredicate()));
    }

    if (!predicatesFiles.isEmpty()) {
      readPrecisionTimer.start();
      PredicateMapParser parser = new PredicateMapParser(config, cfa, logger, formulaManagerView, abstractionManager);
      GlobalInfo.getInstance().predicateMapParser = parser;
      for (Path predicatesFile : predicatesFiles) {
        try {
          result = result.mergeWith(parser.parsePredicates(predicatesFile));

        } catch (IOException e) {
          logger.logUserException(Level.WARNING, e, "Could not read predicate map from file");

        } catch (PredicateParsingFailedException e) {
          logger.logUserException(Level.WARNING, e, "Could not read predicate map");
        }
      }
      readPrecisionTimer.stop();
    }

    return result;
  }

  public Timer getReadPrecisionTimer() {
    return readPrecisionTimer;
  }

  /**
   * Read the (initial) precision (predicates to track) from a file.
   *
   * @return      Precision
   * @throws      InvalidConfigurationException
   */
  public PredicatePrecision prepareInitialPredicates() throws InvalidConfigurationException {
    PredicatePrecision result = internalPrepareInitialPredicates();

    statistics.addKeyValueStatistic("Init. global predicates", result.getGlobalPredicates().size());
    statistics.addKeyValueStatistic("Init. location predicates", result.getLocalPredicates().size());
    statistics.addKeyValueStatistic("Init. function predicates", result.getFunctionPredicates().size());

    GlobalInfo.getInstance().emptyPrecision = result;
    return result;
  }

  @Override
  public void collectStatistics(Collection<Statistics> pStatsCollection) {
    pStatsCollection.add(statistics);
  }
}
