package org.sosy_lab.cpachecker.cpa.impacted;

import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;

public class SimpleEdge {
    private final String statement;
    private final int predecessor;
    private final int successor;
    /**
     * The edge type we use:
     * BlankEdge,  //"Goto", "Label", "", "Function start dummy edge", "INIT GLOBAL VARS", "__CPAchecker_TMP_0;"
     * AssumeEdge, //"[*]"
     * StatementEdge, //"x = y + 1;", "x = func();"
     * DeclarationEdge, //"int x;", "struct...", "int main()"
     * ReturnStatementEdge,
     * FunctionCallEdge,
     * FunctionReturnEdge
     * CallToReturnEdge,
     * UnknownEdge
     **/
    private final CFAEdgeType type;

    public SimpleEdge(int pred, int succ, String stmt, CFAEdgeType pType) {
        statement = stmt;
        predecessor = pred;
        successor = succ;
        type = pType;
    }

    public String getRawStatement() {
        return statement;
    }
    public int getPredecessor() {
        return  predecessor;
    }
    public int getSuccessor() {
        return successor;
    }
    public CFAEdgeType getEdgeType() {
        return type;
    }

    @Override
    public String toString() {
        return "(" + predecessor + ", " + successor + ") -> " + statement;
    }
}
