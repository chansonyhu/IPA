package org.sosy_lab.cpachecker.cpa.impacted;

import com.google.common.collect.ImmutableSet;
import java.util.HashMap;
import org.sosy_lab.cpachecker.cfa.ast.c.CSimpleDeclaration;
import org.sosy_lab.cpachecker.cfa.ast.c.CVariableDeclaration;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CFunctionEntryNode;
import org.sosy_lab.cpachecker.core.defaults.LatticeAbstractState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.defuse.DefUseDefinition;
import org.sosy_lab.cpachecker.cpa.reachdef.ReachingDefState;

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

public class ImpactedState implements AbstractState {
    private Set<CSimpleDeclaration> impactedVariables = new HashSet<>();
    //private Set<CSimpleDeclaration> initialVariables = new HashSet<>();
    public CFunctionEntryNode entry = null;
    //private final String placeHolder = "000";
    private CFANode node;

    public ImpactedState(Set<CSimpleDeclaration> initialVariables) {

        if(initialVariables != null)
            this.impactedVariables.addAll(initialVariables);
    }

    public ImpactedState(ImpactedState pState) {
        this.impactedVariables.addAll(pState.getImpactedVariables());
        this.node = pState.getCFANode();
    }

    public ImpactedState() {
        node = new CFANode("DUMMY_NODE");
    }

    public Set<CSimpleDeclaration> getImpactedVariables() {
        return  impactedVariables;
    }

    public void addImpactedVariable(CSimpleDeclaration iv) {
        impactedVariables.add(iv);
    }

    public void addImpactedVariables(Set<CSimpleDeclaration> ivs) {
        int loc = this.node.getNodeNumber();
        HashMap<Integer, Set<CSimpleDeclaration>> cfa2iv = ImpactedHelper.getInstance().cfa2iv;
        Set<CSimpleDeclaration> prevIV;

        if(!cfa2iv.containsKey(loc))
            cfa2iv.put(loc, new HashSet<>());
        prevIV = cfa2iv.get(loc);
        int prevSize = prevIV.size();
        prevIV.addAll(ivs);
        int currentSize = prevIV.size();
        if(currentSize > prevSize)
            ImpactedHelper.getInstance().isFixed = false;
//        if(currentSize > 0)
//            System.out.println("current size of impacted vars of node " + loc + " is " + currentSize);
        impactedVariables.addAll(ivs);
    }

    public void removeImpactedVariable(CSimpleDeclaration iv) {
        impactedVariables.remove(iv);
    }

    public void setCFANode(CFANode node){
        this.node = node;
    }

    public CFANode getCFANode() {
        return node;
    }

    @Override
    public int hashCode() {
        return impactedVariables.hashCode();
    }

    @Override
    public boolean equals(Object other) {
        if (!(other instanceof ImpactedState)) {
            return false;
        }

        ImpactedState otherDef = (ImpactedState) other;
        return otherDef.impactedVariables.equals(this.impactedVariables);
    }
}
