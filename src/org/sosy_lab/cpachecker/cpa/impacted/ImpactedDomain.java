package org.sosy_lab.cpachecker.cpa.impacted;

import org.sosy_lab.cpachecker.cfa.ast.c.CSimpleDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.core.interfaces.AbstractDomain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.defuse.DefUseDefinition;
import org.sosy_lab.cpachecker.cpa.defuse.DefUseState;

import java.util.HashSet;
import java.util.Set;

public class ImpactedDomain implements AbstractDomain {
    @Override
    public boolean isLessOrEqual(AbstractState element1, AbstractState element2) {
        ImpactedState impactedState1 = (ImpactedState) element1;
        ImpactedState impactedState2 = (ImpactedState) element2;
//        for(CSimpleDeclaration iv : impactedState2.getImpactedVariables())
//            System.out.print(iv == null ? "null" : iv.getQualifiedName() + ", ");
//        System.out.println();
//        System.out.println("Check node " + ((ImpactedState) element1).getCFANode().getNodeNumber() + ": size: " + impactedState2.getImpactedVariables().size()
//            + "; isStop? " +
//            impactedState2.getImpactedVariables().containsAll(impactedState1.getImpactedVariables()));
        return impactedState2.getImpactedVariables().containsAll(impactedState1.getImpactedVariables());
    }
    @Override
    public AbstractState join(AbstractState element1, AbstractState element2) {
        // Useless code, but helps to catch bugs by causing cast exceptions
        ImpactedState impactedState1 = (ImpactedState) element1;
        ImpactedState impactedState2 = (ImpactedState) element2;

        ImpactedState joined = new ImpactedState(new HashSet<CSimpleDeclaration>());
        assert ((ImpactedState) element1).getCFANode().equals(((ImpactedState) element2).getCFANode());
        joined.setCFANode(((ImpactedState) element1).getCFANode());
        joined.addImpactedVariables(((ImpactedState) element1).getImpactedVariables());
        joined.addImpactedVariables(((ImpactedState) element2).getImpactedVariables());
        return joined;
    }
}
