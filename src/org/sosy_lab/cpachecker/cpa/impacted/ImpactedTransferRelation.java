package org.sosy_lab.cpachecker.cpa.impacted;

import static com.google.common.base.Preconditions.checkArgument;
import static org.sosy_lab.cpachecker.cfa.model.CFAEdgeType.DeclarationEdge;

import com.google.common.base.Preconditions;
import javax.lang.model.type.DeclaredType;
import org.jaxen.util.SingletonList;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.time.Timer;
import org.sosy_lab.cpachecker.cfa.ast.c.*;
import org.sosy_lab.cpachecker.cfa.model.*;
import org.sosy_lab.cpachecker.cfa.model.c.*;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.defaults.SingleEdgeTransferRelation;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.ProgramInfo;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;

import java.util.*;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;

public class ImpactedTransferRelation  extends SingleEdgeTransferRelation {

    private CFANode main;
    private Map<String, Set<CSimpleDeclaration>> reductionVariables = new HashMap<>();
    public static org.sosy_lab.common.time.Timer totalPostTime = new Timer();
//    @Override
//    public Collection<? extends AbstractState> getAbstractSuccessors(AbstractState pState, Precision pPrecision)
//            throws CPATransferException, InterruptedException {
//        List<AbstractState> successors = new ArrayList<>();
//        return successors;
//    }

    @Override
    public Collection<? extends AbstractState> getAbstractSuccessorsForEdge(
            AbstractState pState, Precision pPrecision, CFAEdge pCfaEdge)
            throws CPATransferException, InterruptedException {
        Preconditions.checkNotNull(pCfaEdge);
        if(CPAMain.isDebug)
            return Collections.emptyList();
        if(ImpactedHelper.getInstance().invariantsFile.toString().contains("null.txt"))
            return Collections.singleton(new ImpactedState());
        return getAbstractSuccessors0(pState, pCfaEdge);
    }

    private Collection<? extends AbstractState> getAbstractSuccessors0(AbstractState pState, CFAEdge pCfaEdge) throws CPATransferException {
        if(ImpactedHelper.getInstance().readyForAnalysis)
            return Collections.singleton(new ImpactedState());
        //logger.log(Level.FINE, "Compute successor for ", pState, "along edge", pCfaEdge);
        if(pCfaEdge.getEdgeType() == DeclarationEdge) {
            ImpactedState result = new ImpactedState((ImpactedState) pState);
            result.setCFANode(pCfaEdge.getSuccessor());
            result.addImpactedVariables(result.getCFANode().impactedVariables);
            return Collections.singleton(result);
            // return Collections.singleton(new ImpactedState());
        }
        totalPostTime.start();
        try {
            if (!(pState instanceof ImpactedState)) {
                throw new CPATransferException(
                        "Unexpected type of abstract state. The transfer relation is not defined for this type");
            }

            if (pCfaEdge == null) {
                throw new CPATransferException(
                        "Expected an edge along which the successors should be computed");
            }

//        if (pState == ImpactedState.topElement) {
//            return Collections.singleton(pState);
//        }

            ImpactedState result = new ImpactedState((ImpactedState) pState);
            result.setCFANode(pCfaEdge.getSuccessor());
            result.addImpactedVariables(result.getCFANode().impactedVariables);
            assert !result.getImpactedVariables().contains(null);

            switch (pCfaEdge.getEdgeType()) {
                case StatementEdge: {
                    result = handleStatementEdge(result, (CStatementEdge) pCfaEdge);
                    break;
                }
                case DeclarationEdge: {
                    result = handleDeclarationEdge(result, (CDeclarationEdge) pCfaEdge);
                    break;
                }
                case FunctionCallEdge: {
                    if (pCfaEdge.getSuccessor() instanceof CFunctionEntryNode) {
                        addReductionVariables(result, pCfaEdge);
                    }
                    result = handleCallEdge(result, ((CFunctionCall) ((CFunctionCallEdge) pCfaEdge).getFunctionCall()));
                    break;
                }
                case FunctionReturnEdge: {
                    result = handleFunctionReturnEdge(result, pCfaEdge);
                    break;
                }
                //TODO qianshan for bam
                case MultiEdge: {
                    //result = (ImpactedState)pState;
                    result = handleMultiEdge(result, (MultiEdge) pCfaEdge);
                    break;
                }
                case BlankEdge:
                    // TODO still correct?
                    result = handleBlankEdge(result, pCfaEdge);
                    break;
                //$FALL-THROUGH$
                case AssumeEdge: {
                    result = handleAssumeEdge(result, (CAssumeEdge) pCfaEdge);
                    break;
                }
                case CallToReturnEdge:
                case ReturnStatementEdge:
                    result = handleReturnEdge(result, (CReturnStatementEdge) pCfaEdge);
                    //logger.log(Level.FINE, "Reaching definition not affected by edge. ", "Keep reaching definition unchanged.");
                    //result = (ImpactedState) result;
                    break;
                default:
                    throw new CPATransferException("Unknown CFA edge type.");
            }
            if(result.getImpactedVariables().size() > 0) {
                result.getCFANode().impactedVariables.addAll(result.getImpactedVariables());
                CFANode node = result.getCFANode();
                int loc = node.getNodeNumber();
                HashMap<Integer, Set<CSimpleDeclaration>> cfa2iv =
                    ImpactedHelper.getInstance().cfa2iv;
                Set<CSimpleDeclaration> prevIV;
                if (!cfa2iv.containsKey(loc))
                    cfa2iv.put(loc, new HashSet<>());
                prevIV = cfa2iv.get(loc);
                int prevSize = prevIV.size();
                prevIV.addAll(result.getImpactedVariables());
                int currentSize = prevIV.size();
                if (currentSize > prevSize)
                    ImpactedHelper.getInstance().isFixed = false;
            }
            return Collections.singleton(result);
        } finally {
            totalPostTime.stop();
        }
    }

    private void addReductionVariables(ImpactedState result, CFAEdge pCfaEdge) {
        result.entry = (CFunctionEntryNode) pCfaEdge.getSuccessor();
        String funcName = result.entry.getFunctionName();
        if(result.getImpactedVariables().size() > 0) {
            result.entry.reductionVariables.addAll(result.getImpactedVariables());
            if(!reductionVariables.containsKey(funcName)) {
                reductionVariables.put(funcName, new HashSet<>());
            }
            Set<CSimpleDeclaration> vars = reductionVariables.get(funcName);
            vars.addAll(result.getImpactedVariables());
        }
    }

    private ImpactedState handleStatementEdge(ImpactedState pState, CStatementEdge edge)
            throws CPATransferException {
        CStatement statement = edge.getStatement();
        switch (statement.getClass().getSimpleName()) {
            case "CExpressionAssignmentStatement": {
                CSimpleDeclaration left;
                CExpression rawLeft = ((CExpressionAssignmentStatement) (statement)).getLeftHandSide();

                left = getIV(rawLeft, true);
//                if(rawLeft instanceof CPointerExpression) {
//                    tmp = ((CPointerExpression) rawLeft).getOperand();
//                    if(tmp instanceof CIdExpression) {
//                        left = (CIdExpression) tmp;
//                    } else if(tmp instanceof CCastExpression){
//                        left = (CIdExpression) ((CCastExpression) tmp).getOperand();
//                    } else {
//                        //TODO qianshan impacted incomplete
//                    }
//                } else {
//                    CExpression Left = (CExpression) ((CExpressionAssignmentStatement) statement).getLeftHandSide();
//                    if(Left instanceof CFieldReference) {
//                        CExpression owner = ((CFieldReference) Left).getFieldOwner();
//                        if(owner instanceof CIdExpression) {
//                            left = (CIdExpression) owner;
//                        } else if(owner instanceof CCastExpression) {
//                            left = (CIdExpression) ((CCastExpression) owner).getOperand();
//                        }
//                    } else if(Left instanceof CArraySubscriptExpression) {
//                        CExpression arrayLeft = ((CArraySubscriptExpression) Left).getArrayExpression();
//                        if(arrayLeft instanceof CFieldReference) {
//                            CExpression owner = ((CFieldReference) arrayLeft).getFieldOwner();
//                            if(owner instanceof CIdExpression) {
//                                left = (CIdExpression) owner;
//                            } else if(owner instanceof CCastExpression) {
//                                left = (CIdExpression) ((CCastExpression) owner).getOperand();
//                            }
//                        } else {
//                            left = (CIdExpression) (arrayLeft);
//                        }
//                    } else {
//                        left = (CIdExpression) ((CExpressionAssignmentStatement) (statement)).getLeftHandSide();
//                    }
//                }

                CExpression right = ((CExpressionAssignmentStatement) (statement)).getRightHandSide();
                switch (right.getClass().getSimpleName()) {
                    case "CBinaryExpression": {
                        Set<CSimpleDeclaration> rightVariables = new HashSet<>();
                        CSimpleDeclaration op1 = getIV(((CBinaryExpression) right).getOperand1(), false);
                        CSimpleDeclaration op2 = getIV(((CBinaryExpression) right).getOperand2(), false);
                        if(op1 instanceof CVariableDeclaration) {
                            rightVariables.add(op1);
                        }
                        if(op2 instanceof CVariableDeclaration) {
                            rightVariables.add(op2);
                        }
                        if (pState.getImpactedVariables().contains(left))
                            return pState;
                        for (CSimpleDeclaration iv : pState.getImpactedVariables()) {
                            if (rightVariables.contains(iv)) {
                                pState.addImpactedVariable(left);
                                break;
                            }
                        }

                    }
                    break;
                }
            }
            break;
            case "CFunctionCallAssignmentStatement": {
                handleCallEdge((ImpactedState) pState, ((CFunctionCallAssignmentStatement) statement));
            }
            break;

        }
        CExpression left;
        // TODO

        return pState;

    }

    private ImpactedState handleAssumeEdge(ImpactedState pState, CAssumeEdge edge) {
        boolean isImpacted = addIVForAssumeEdge(pState, edge, false);

        if(edge.isImpacted && !isImpacted) {
            isImpacted = true;
            addIVForAssumeEdge(pState, edge, edge.isImpacted);
        }

        if(isImpacted) {
            assert edge.getSuccessor().getNumLeavingEdges() == 1;
            CFAEdge succ = edge.getSuccessor().getLeavingEdge(0);
            if(succ instanceof MultiEdge) {
                MultiEdge body = (MultiEdge) edge.getSuccessor().getLeavingEdge(0);
                for (CFAEdge e : body.getEdges()) {
                    if (e.getEdgeType().equals(CFAEdgeType.StatementEdge)) {
                        CStatement statement = ((CStatementEdge) e).getStatement();
                        if (statement instanceof CExpressionAssignmentStatement) {
                            CExpression tmpLeft = ((CExpressionAssignmentStatement) statement).getLeftHandSide();
                            CIdExpression left = null;
                            if(tmpLeft instanceof CPointerExpression) {
                                CExpression tmp;
                                tmp = ((CPointerExpression) tmpLeft).getOperand();
                                if(tmp instanceof CCastExpression) {
                                    left = (CIdExpression) ((CCastExpression) tmp).getOperand();
                                } else {
                                    left = (CIdExpression) tmp;
                                }
                            } else {
                                left = (CIdExpression) ((CExpressionAssignmentStatement) (statement)).getLeftHandSide();
                            }
                            pState.addImpactedVariable(left.getDeclaration());
                        }
                    }
                }
            }
        }
        return pState;
    }

    private boolean addIVForAssumeEdge(ImpactedState pState, CAssumeEdge edge,
                                       boolean edgeChanged) {
        CExpression condition = edge.getExpression();
        boolean isImpacted = false;
        if(condition instanceof CBinaryExpression) {
            CExpression op1 = ((CBinaryExpression) condition).getOperand1();
            CExpression op2 = ((CBinaryExpression) condition).getOperand2();
            if(op1 instanceof CIdExpression ) {
                if(pState.getImpactedVariables().contains(((CIdExpression)op1).getDeclaration()) || edgeChanged) {
                    isImpacted = true;
                    pState.addImpactedVariable( ((CIdExpression)op1).getDeclaration() );
                    if(op2 instanceof CBinaryExpression) {
                        CExpression _op1 = ((CBinaryExpression) op2).getOperand1();
                        CExpression _op2 = ((CBinaryExpression) op2).getOperand2();
                        if(_op1 instanceof CIdExpression)
                            pState.addImpactedVariable(((CIdExpression) _op1).getDeclaration());
                        if(_op2 instanceof CIdExpression)
                            pState.addImpactedVariable(((CIdExpression) _op2).getDeclaration());
                    } else if(op2 instanceof CIdExpression) {
                        pState.addImpactedVariable( ((CIdExpression)op2).getDeclaration() );
                    }
                }
            }
            if(op2 instanceof CIdExpression) {
                if(pState.getImpactedVariables().contains(((CIdExpression)op2).getDeclaration()) || edgeChanged) {
                    isImpacted = true;
                    if(op1 instanceof CIdExpression)
                        pState.addImpactedVariable( ((CIdExpression)op1).getDeclaration() );
                    pState.addImpactedVariable( ((CIdExpression)op2).getDeclaration() );
                }
            }
        } //else if () {
        return isImpacted;
    }
    static CSimpleDeclaration getIV(CExpression pkey, boolean isLeft) {
        if(pkey instanceof CFieldReference) {
            return ImpactedHelper.getInstance().getFieldDeclaration((CFieldReference) pkey);
        }

        CExpression exp;
        CSimpleDeclaration key = null;
        exp = ImpactedHelper.getInstance().getProperLeftHand(pkey);
        if(exp == null) {
            return null;
        } else if(exp instanceof CIdExpression) {
            key = ((CIdExpression) exp).getDeclaration();
        } else if(exp instanceof CBinaryExpression) {
            if(isLeft) {
                //qianshan bug fix: *(data + 3UL), we want data
                //qianshan bug fix: *(((msgs + (((unsigned long)i) + 1UL))->buf) + ((unsigned long)j))
                CExpression tmpExp = ((CBinaryExpression) exp).getOperand1();
                tmpExp = ImpactedHelper.getInstance().getProperLeftHand(tmpExp);
                if(tmpExp instanceof  CFieldReference) {
                    return ImpactedHelper.getInstance().getFieldDeclaration((CFieldReference) tmpExp);
                }
                if(tmpExp instanceof CBinaryExpression) {
                    tmpExp = ((CBinaryExpression) tmpExp).getOperand1();
                }
//                if(!(tmpExp instanceof CIdExpression)) {
//                    System.out.println(tmpExp.toString());
//                    System.out.println(tmpExp.toASTString());
//                    System.out.println(tmpExp.getClass());
//                }
                checkArgument(tmpExp instanceof CIdExpression);
                key = ((CIdExpression) tmpExp).getDeclaration();
            } else {
                return null;
            }
        }

        return key;
    }

    private ImpactedState handleDeclarationEdge(ImpactedState pState, CDeclarationEdge edge)
            throws CPATransferException {

        return pState;
    }

    private ImpactedState handleCallEdge(ImpactedState pState, CFunctionCall stmt) {
        CSimpleDeclaration left = null;
        CFunctionCallExpression right = null;
        boolean isAssign = true;

        if(stmt instanceof CFunctionCallAssignmentStatement) {
            CExpression rawLeft = ((CFunctionCallAssignmentStatement) (stmt)).getLeftHandSide();

            left = getIV(rawLeft, true);

            right = ((CFunctionCallAssignmentStatement) (stmt)).getRightHandSide();
        } else if(stmt instanceof CFunctionCallStatement) {
            right = (CFunctionCallExpression) stmt.getFunctionCallExpression();
            isAssign = false;
        }
        //TODO need to adopt a full impact analysis to function body
        if(ProgramInfo.getInstance().getChangedFunSet().contains(right.getFunctionNameExpression().toString()) &&
                isAssign) {
            pState.addImpactedVariable(left);
            return pState;
        }

        HashMap<CSimpleDeclaration, CParameterDeclaration> paraMap = new HashMap<>();
        List<CExpression> actual_paras = right.getParameterExpressions();
        if(right.getDeclaration() != null) {
            List<CParameterDeclaration> formal_paras = right.getDeclaration().getParameters();
            for (int i = 0; i < formal_paras.size(); i++) {
                //TODO qianshan impacted handle reference
                CExpression pkey = actual_paras.get(i);
                CSimpleDeclaration key;

                key = getIV(pkey, false);

                if (key != null)
                    paraMap.put(key, formal_paras.get(i));
            }
        }

        Set<CSimpleDeclaration> impacted_tmp = new HashSet<>(pState.getImpactedVariables());
        if(pState.getCFANode() instanceof CFunctionEntryNode) {
            //remove non-global variables
            for (CSimpleDeclaration iv : impacted_tmp) {
                if (iv instanceof CVariableDeclaration) {
                    if (!((CVariableDeclaration) iv).isGlobal()) {
                        pState.removeImpactedVariable(iv);
                        pState.addImpactedVariable(paraMap.get(iv));
                    }
                } else if (iv instanceof CParameterDeclaration) {
                    pState.removeImpactedVariable(iv);
                }
            }
        }

        for(CExpression ap : actual_paras) {
            //TODO qianshan impacted handle reference
            CExpression pkey = ap;
            CSimpleDeclaration vd;

            vd = getIV(pkey, false);

            if(pState.getImpactedVariables().contains(vd)) {
                pState.addImpactedVariable(paraMap.get(vd));
            }
        }

        Set<CSimpleDeclaration> tmp = new HashSet<>(pState.getImpactedVariables());
        for(CSimpleDeclaration iv : tmp) {
            if(iv == null)
                pState.removeImpactedVariable(iv);
        }
        if(impacted_tmp.size() > 0 && pState.getImpactedVariables().size() == 0) {
            pState.addImpactedVariable(IncrementalPAUtil.getInstance().dummyVariable);
        }

//        for(CExpression v : right.getParameterExpressions()) {
//            if(v instanceof CIdExpression) {
//                for(CSimpleDeclaration iv : pState.getImpactedVariables()) {
//                    if(iv.equals(((CIdExpression) v).getDeclaration())) {
//                        pState.addImpactedVariable((CSimpleDeclaration) left.getDeclaration());
//                        return pState;
//                    }
//                }
//            }
//        }
        return pState;
    }

    private ImpactedState handleReturnEdge(ImpactedState pState, CReturnStatementEdge pCfaEdge) {
        if(!pCfaEdge.getRawAST().get().asAssignment().isPresent()) return pState;
        CExpressionAssignmentStatement rt = (CExpressionAssignmentStatement)(pCfaEdge.getRawAST().get()).asAssignment().get();
        CExpression right = rt.getRightHandSide();
        CExpression left = rt.getLeftHandSide();
        if(right instanceof CIdExpression) {
            if(pState.getImpactedVariables().contains(((CIdExpression) right).getDeclaration())) {
                pState.addImpactedVariable(((CIdExpression)left).getDeclaration());
            }
        }
        return pState;
    }

    private ImpactedState handleFunctionReturnEdge(ImpactedState pState, CFAEdge edge) {
        //handle function return statement

        //handle function return

        CSimpleDeclaration left = null;
        CFunctionCallExpression right = null;
        CFunctionCall rtExp = ((CFunctionReturnEdge) edge).getSummaryEdge().getExpression();
        boolean isAssign = true;
        if(rtExp instanceof CFunctionCallAssignmentStatement) {

            CExpression rawLeft = ((CFunctionCallAssignmentStatement) (rtExp)).getLeftHandSide();

            left = getIV(rawLeft, true);

            right = ((CFunctionCallAssignmentStatement) (rtExp)).getRightHandSide();
        } else if(rtExp instanceof CFunctionCallStatement) {
            right = (CFunctionCallExpression) rtExp.getFunctionCallExpression();
            isAssign = false;
        }

        HashMap<CParameterDeclaration, CSimpleDeclaration> paraMap = new HashMap<>();
        List<CParameterDeclaration> formal_paras = right.getDeclaration().getParameters();
        List<CExpression> actual_paras = right.getParameterExpressions();
        for(int i = 0; i < formal_paras.size(); i++) {
            CSimpleDeclaration value;
            value = getIV(actual_paras.get(i), false);
            paraMap.put(formal_paras.get(i), value);
        }

        //remove non-global variables
        Set<CSimpleDeclaration> tmp = new HashSet<>(pState.getImpactedVariables());
        for (CSimpleDeclaration iv : tmp) {
            if(iv == null) continue;
            if(iv instanceof CParameterDeclaration) {
                pState.removeImpactedVariable(iv);
                continue;
            }
            CSimpleDeclaration ivd;
            if(iv instanceof CFieldDeclaration)
                ivd = ((CFieldDeclaration) iv).getDeclaration();
            else
                ivd = iv;
            checkArgument(ivd instanceof CVariableDeclaration || ivd instanceof CParameterDeclaration || ivd instanceof CDummyDeclaration);
            if(ivd instanceof CParameterDeclaration) {
                pState.removeImpactedVariable(ivd);
                continue;
            } else if(ivd instanceof CDummyDeclaration) {
                // do nothing
            } else if (!((CVariableDeclaration) ivd).isGlobal()) {
                //continue;
                if(!(iv).getName().equals("__retval__"))
                    pState.removeImpactedVariable(iv);
            }

        }
        for(CSimpleDeclaration iv : tmp) {
            if(iv == null) continue;
            if (iv instanceof CParameterDeclaration) {
                pState.addImpactedVariable(paraMap.get(iv));
            } else if(iv.getName().equals("__retval__") && isAssign) {
                pState.removeImpactedVariable(iv);
                pState.addImpactedVariable(left);
            }
        }

        //TODO expand
        CFunctionEntryNode entry = ((CFunctionReturnEdge) edge).getSummaryEdge().getFunctionEntry();
        Set<CSimpleDeclaration> vars = null;
        String functionName = entry.getFunctionName();
        if(reductionVariables.containsKey(functionName)) {
            vars = reductionVariables.get(functionName);
        }
        if(vars != null && vars.size() > 0) {
            pState.addImpactedVariables(vars);
            vars.clear();
        }
        Set<CSimpleDeclaration> curImpacted = pState.getImpactedVariables();
        if(curImpacted.contains(IncrementalPAUtil.getInstance().dummyVariable)) {
            curImpacted.remove(IncrementalPAUtil.getInstance().dummyVariable);
        }
        return pState;
    }

    private ImpactedState handleMultiEdge(ImpactedState pState, MultiEdge edge) throws CPATransferException {
        ImpactedState result = pState;
        for (final CFAEdge innerEdge : edge.getEdges()) {
            switch (innerEdge.getEdgeType()) {
                case StatementEdge: {
                    result = handleStatementEdge((ImpactedState) result, (CStatementEdge) innerEdge);
                    break;
                }
                case DeclarationEdge: {
                    result = handleDeclarationEdge((ImpactedState) result, (CDeclarationEdge) innerEdge);
                    break;
                }
                case FunctionCallEdge: {
                    if(innerEdge.getSuccessor() instanceof CFunctionEntryNode) {
                        addReductionVariables(result, innerEdge);
                    }
                    result = handleCallEdge((ImpactedState) result,
                            ((CFunctionCallAssignmentStatement)((CFunctionCallEdge) innerEdge).getFunctionCall()));
                    break;
                }
                case FunctionReturnEdge: {
                    result = handleFunctionReturnEdge((ImpactedState) result, innerEdge);
                    break;
                }
                //TODO qianshan for bam
                case MultiEdge: {
                    //result = (ImpactedState)pState;
                    result = handleMultiEdge((ImpactedState) result, (MultiEdge) innerEdge);
                    break;
                }
                case BlankEdge:
                    // TODO still correct?
                    result = handleBlankEdge(result, innerEdge);
                    break;
                //$FALL-THROUGH$
                case AssumeEdge: {
                    result = handleAssumeEdge(result, (CAssumeEdge) innerEdge);
                    break;
                }
                case CallToReturnEdge:
                case ReturnStatementEdge:
                    result = handleReturnEdge(result, (CReturnStatementEdge) innerEdge);
                    //logger.log(Level.FINE, "Reaching definition not affected by edge. ", "Keep reaching definition unchanged.");
                    //result = (ImpactedState) result;
                    break;
                default:
                    throw new CPATransferException("Unknown CFA edge type.");
            }


        }
        return result;
    }

    private ImpactedState handleSingleEdge(ImpactedState pState, CFAEdge pCfaEdge) throws CPATransferException {
        ImpactedState result = null;
        switch (pCfaEdge.getEdgeType()) {
            case StatementEdge: {
                result = handleStatementEdge((ImpactedState) result, (CStatementEdge) pCfaEdge);
                break;
            }
            case DeclarationEdge: {
                result = handleDeclarationEdge((ImpactedState) result, (CDeclarationEdge) pCfaEdge);
                break;
            }
            case FunctionCallEdge: {
                if(pCfaEdge.getSuccessor() instanceof CFunctionEntryNode) {
                    addReductionVariables(result, pCfaEdge);
                }
                result = handleCallEdge((ImpactedState) result,
                        ((CFunctionCallAssignmentStatement)((CFunctionCallEdge) pCfaEdge).getFunctionCall()));
                break;
            }
            case FunctionReturnEdge: {
                result = handleFunctionReturnEdge((ImpactedState) result, pCfaEdge);
                break;
            }
            //TODO qianshan for bam
            case MultiEdge: {
                //result = (ImpactedState)pState;
                result = handleMultiEdge((ImpactedState) result, (MultiEdge) pCfaEdge);
                break;
            }
            case BlankEdge:
                // TODO still correct?
                result = handleBlankEdge(result, pCfaEdge);
                break;
            //$FALL-THROUGH$
            case AssumeEdge: {
                result = handleAssumeEdge(result, (CAssumeEdge) pCfaEdge);
                break;
            }
            case CallToReturnEdge:
            case ReturnStatementEdge:
                result = handleReturnEdge(result, (CReturnStatementEdge) pCfaEdge);
                //logger.log(Level.FINE, "Reaching definition not affected by edge. ", "Keep reaching definition unchanged.");
                //result = (ImpactedState) result;
                break;
            default:
                throw new CPATransferException("Unknown CFA edge type.");
        }
        return result;
    }
    
    private ImpactedState handleBlankEdge(ImpactedState pState, CFAEdge pEdge) {
        // handle function start dummy edge

        if (pEdge.getSuccessor().isLoopStart()) {
            //&& ((ReachingDefState) pState).getLocalReachingDefinitions().size() == 0) {
            // result = ((ReachingDefState) pState).initVariables(localVariablesPerFunction.get(pCfaEdge.getPredecessor()),
            //        ImmutableSet.copyOf(((FunctionEntryNode) pCfaEdge.getPredecessor()).getFunctionParameterNames()),
            //       pCfaEdge.getPredecessor(), pCfaEdge.getSuccessor());
            CFANode loopStartNode = pEdge.getSuccessor();
            CAssumeEdge trueEdge;
            if(loopStartNode.getNumLeavingEdges() == 1 || loopStartNode instanceof CLabelNode) {
                trueEdge = null;
                return pState;
            } else {
                trueEdge = ((CAssumeEdge) loopStartNode.getLeavingEdge(0));
            }
            assert trueEdge.getTruthAssumption() == true;
            if(pState.getCFANode().equals(loopStartNode)) {
                //join operator
            }
            CExpression condition = trueEdge.getExpression();
            boolean isImpacted = false;
            if(condition instanceof CBinaryExpression) {
                CExpression op1 = ((CBinaryExpression) condition).getOperand1();
                CExpression op2 = ((CBinaryExpression) condition).getOperand2();
                if(op1 instanceof CIdExpression ) {
                    if(pState.getImpactedVariables().contains(((CIdExpression)op1).getDeclaration()))
                        isImpacted = true;
                }
                if(op2 instanceof CIdExpression) {
                    if(pState.getImpactedVariables().contains(((CIdExpression)op2).getDeclaration()))
                        isImpacted = true;
                }
            } //else if () {

            //}
            if(isImpacted) {
                assert trueEdge.getSuccessor().getNumLeavingEdges() == 1;
                MultiEdge loopBody = (MultiEdge) trueEdge.getSuccessor().getLeavingEdge(0);
                for(CFAEdge e : loopBody.getEdges()) {
                    if (e.getEdgeType().equals(CFAEdgeType.StatementEdge)) {
                        CStatement statement = ((CStatementEdge) e).getStatement();
                        if (statement instanceof CExpressionAssignmentStatement) {

                            CExpression tmpLeft = ((CExpressionAssignmentStatement) statement).getLeftHandSide();
                            CSimpleDeclaration sd = getIV(tmpLeft, true);

                            pState.addImpactedVariable(sd);
                        }
                    }
                }
            }
        }
        return pState;
    }


    @Override
    public Collection<? extends AbstractState> strengthen(AbstractState element,
                                                          List<AbstractState> otherElements, CFAEdge cfaEdge,
                                                          Precision precision) {
        return null;
    }
}
