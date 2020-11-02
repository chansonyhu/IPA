package org.sosy_lab.cpachecker.cpa.impacted;

import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.c.CSimpleDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionEntryNode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.defaults.AbstractCPA;
import org.sosy_lab.cpachecker.core.defaults.AutomaticCPAFactory;
import org.sosy_lab.cpachecker.core.defaults.DelegateAbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.*;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.ProgramInfo;
import org.sosy_lab.cpachecker.cpa.defuse.DefUseDefinition;
import org.sosy_lab.cpachecker.cpa.defuse.DefUseDomain;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateCPA;
import org.sosy_lab.cpachecker.cpa.reachdef.ReachingDefState;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.BlockOperator;
import org.sosy_lab.cpachecker.util.predicates.Solver;
import org.sosy_lab.cpachecker.util.predicates.SymbolicRegionManager;
import org.sosy_lab.cpachecker.util.predicates.bdd.BDDManagerFactory;
import org.sosy_lab.cpachecker.util.predicates.interfaces.PathFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.RegionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormulaManagerImpl;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

@Options(prefix = "cpa.impacted")
public class ImpactedCPA extends AbstractCPA implements StatisticsProvider {

    @Option(secure=true, name="merge", toUppercase=true, values={"SEP", "JOIN", "IGNORECALLSTACK"},
            description="which merge operator to use for ImpactedCPA")
    private String mergeType = "JOIN";

    @Option(secure=true, name="stop", toUppercase=true, values={"SEP", "JOIN", "IGNORECALLSTACK"},
            description="which stop operator to use for ImpactedCPA")
    private String stopType = "SEP";

//    @Option(secure = true, description = "invariants as disjunction formula",
//            name = "invariants.disjunction")
//    public boolean isInvDisj = false;

    private final Solver solver;
    protected final LogManager logger;
    private final ImpactedCPAStatistics stats;

    public static CPAFactory factory() {
        return AutomaticCPAFactory.forType(ImpactedCPA.class);
    }

    private ImpactedCPA(Configuration config, LogManager logger,
                        ShutdownNotifier pShutdownNotifier) throws InvalidConfigurationException {
        super(
                "irrelevant", // operator-initialization is overridden
                "SEP",
                new ImpactedDomain(),
                new ImpactedTransferRelation());
        config.inject(this);
        this.logger = logger;
        solver = Solver.create(config, logger, pShutdownNotifier);

        stats = new ImpactedCPAStatistics(this, config, GlobalInfo.getInstance().getAbstractionManager(),
                GlobalInfo.getInstance().getRegionManager());
    }


    @Override
    public MergeOperator getMergeOperator() {
        return buildMergeOperator(mergeType);
    }

    @Override
    public StopOperator getStopOperator() {
        return buildStopOperator(stopType);
    }

    @Override
    public AbstractState getInitialState(CFANode pNode, StateSpacePartition pPartition) {
        //TODO
        List<String> parameterNames = null;
        Set<CSimpleDeclaration> tmp = new HashSet<>();
        if (pNode instanceof CFunctionEntryNode) {
            parameterNames = ((CFunctionEntryNode) pNode).getFunctionParameterNames();
        }
        return new ImpactedState(tmp);
    }

    public Solver getSolver() {
        return solver;
    }

    public LogManager getLogger() {
        return logger;
    }

    @Override
    public void collectStatistics(Collection<Statistics> pStatsCollection) {
        pStatsCollection.add(stats);
        //precisionBootstraper.collectStatistics(pStatsCollection);
        //if (invariantGenerator instanceof StatisticsProvider) {
        //    ((StatisticsProvider)invariantGenerator).collectStatistics(pStatsCollection);
        //}
        solver.collectStatistics(pStatsCollection);
    }
}
