package org.sosy_lab.cpachecker.cpa.impacted;

import com.google.common.base.Optional;
import com.google.common.collect.*;
import org.sosy_lab.common.Pair;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.ast.c.*;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.c.CAssumeEdge;
import org.sosy_lab.cpachecker.cfa.model.c.CStatementEdge;
import org.sosy_lab.cpachecker.util.CFAUtils;
import org.sosy_lab.cpachecker.util.LoopStructure;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;

public class ImpactedCFAUtils {
    private static HashSet<CFAEdge> visitedEdges = new HashSet<>();

    public static void traverse_new(CFA cfa) {
        Set<CFANode> visitedNodes = new HashSet<>();
        CFANode root = cfa.getMainFunction();
        Deque<CFANode> waitingNodeList = new ArrayDeque<>();
        ArrayList<CFAEdge> waitingEdgeList = new ArrayList<>();
        //final Optional<ImmutableSet<CFANode>> loopHeads = cfa.getAllLoopHeads();
        //final Optional<LoopStructure> loopStructure = cfa.getLoopStructure();

        waitingNodeList.add(root);
        while (!waitingNodeList.isEmpty()) {
            CFANode node = waitingNodeList.poll();
            //System.out.println("Impacted traverse node: " + node.getNodeNumber());
            if (visitedNodes.add(node)) {
                Iterables.addAll(waitingNodeList, CFAUtils.successorsOf(node));
                //Iterables.addAll(waitingNodeList, CFAUtils.predecessorsOf(node)); // just to be sure to get ALL nodes.

                Iterables.addAll(waitingEdgeList, CFAUtils.allLeavingEdges(node).toList());


            }
        }
        // The actual checks
        checkChanges(waitingEdgeList);
    }

    private static void checkChanges(ArrayList<CFAEdge> edges) {
        SimpleEdge oriEdge;


        for(CFAEdge edge :edges) {
            if((isModified(edge) || isAdded(edge)) && !visitedEdges.contains(edge)) {
                oriEdge = getOriginalEdge(edge);
                decideIVonSucc(oriEdge, edge);
            }
            visitedEdges.add(edge);
        }
    }

    public static void traverse(CFA cfa) {
        //handle added and modified edges
        //遇到Assume Edge和loop Edge需要遍历整个block，之前的算法没有实现
        CFANode root = cfa.getMainFunction();
        Set<CFAEdge> visitedEdges = new HashSet<>();
        ArrayDeque<CFAEdge> waitingEdgeList = new ArrayDeque<>();
        final Optional<ImmutableSet<CFANode>> loopHeads = cfa.getAllLoopHeads();
        final Optional<LoopStructure> loopStructure = cfa.getLoopStructure();


        //waitingNodeList.add(root);
        waitingEdgeList.addAll(CFAUtils.allLeavingEdges(root).toList());
        while (!waitingEdgeList.isEmpty()) {
            //CFANode node = waitingNodeList.poll();
            CFAEdge edge = waitingEdgeList.poll();
            CFANode node = edge.getSuccessor();

            int oldSize = waitingEdgeList.size();
            int newSize = -1;
            while(oldSize != newSize) {
                oldSize = waitingEdgeList.size();
                for (CFAEdge pEdge : waitingEdgeList) {
                    if (visitedEdges.contains(pEdge)) {
                        waitingEdgeList.remove(pEdge);
                    }
                }
                newSize = waitingEdgeList.size();
            }

            if(!(isAdded(edge) || isModified(edge))) {
                // we only handle added and modified edges
                ImmutableList<CFAEdge> leavingEdges = CFAUtils.allLeavingEdges(node).toList();
                for(CFAEdge pEdge : leavingEdges) {
                    if(!visitedEdges.contains(pEdge)) {
                        waitingEdgeList.add(pEdge);
                    }
                }
                System.out.println("infinite loop");
                //waitingEdgeList.addAll(CFAUtils.allLeavingEdges(node).toList());
                continue;
            }

            SimpleEdge oriEdge = null;

            if(isModified(edge)) {
                oriEdge = getOriginalEdge(edge);
            }

            if(loopHeads.isPresent() && (loopHeads.get().contains(node) || node.isLoopStart())) {
                //TODO decide IV of loop
                ImmutableSet<LoopStructure.Loop> loop = ImmutableSet.of();
                if(loopStructure.isPresent()) {
                    loop = loopStructure.get().getLoopsForLoopHead(node);
                }
                LoopStructure.Loop l = loop.asList().get(0);
                ImmutableSet<CFAEdge> loopEdges = l.getInnerLoopEdges();

                for (CFAEdge loopEdge : loopEdges) {
                    if(loopEdge.getEdgeType() == CFAEdgeType.AssumeEdge) {
                        if (visitedEdges.add(loopEdge)) {
                            decideIVonSucc(oriEdge, loopEdge);
                        }
                    }
                }
                ImmutableList<CFAEdge> leavingEdges = CFAUtils.allLeavingEdges(node).toList();
                for(CFAEdge pEdge : leavingEdges) {
                    if(!visitedEdges.contains(pEdge)) {
                        waitingEdgeList.add(pEdge);
                    }
                }
                //waitingEdgeList.addAll(CFAUtils.allLeavingEdges(node).toList());

            }

            if(isIfNode(node)) {
                //TODO decide IV of if statement
                FluentIterable<CFAEdge> succs = CFAUtils.allLeavingEdges(node);
                for(CFAEdge succ : succs) {
                    if(succ.getEdgeType() == CFAEdgeType.AssumeEdge) {
                        if (visitedEdges.add(succ)) {
                            decideIVonSucc(oriEdge, succ);
                        }
                    }
                }
                ImmutableList<CFAEdge> leavingEdges = CFAUtils.allLeavingEdges(node).toList();
                for(CFAEdge pEdge : leavingEdges) {
                    if(!visitedEdges.contains(pEdge)) {
                        waitingEdgeList.add(pEdge);
                    }
                }
                //waitingEdgeList.addAll(CFAUtils.allLeavingEdges(node).toList());
            }

            if(visitedEdges.add(edge)) {
                decideIVonSucc(oriEdge, edge);
                ImmutableList<CFAEdge> leavingEdges = CFAUtils.allLeavingEdges(node).toList();
                for(CFAEdge pEdge : leavingEdges) {
                    if(!visitedEdges.contains(pEdge)) {
                        waitingEdgeList.add(pEdge);
                    }
                }
                //waitingEdgeList.addAll(CFAUtils.allLeavingEdges(node).toList());
            }
        }
    }

    public static void handleDeletedEdges() {
        for(Map.Entry<Pair<Integer, Integer>, SimpleEdge> entry : ImpactedHelper.getInstance().cfa_deleted_edges.entrySet()) {
            //TODO qianshan: need to do
            entry.toString();
        }
    }

    private static void decideIVonSucc(SimpleEdge oriEdge, CFAEdge edge) {
        if(isTrivialChange(oriEdge, edge))
            return;
        CFANode pred = edge.getPredecessor();
        CFANode succ = edge.getSuccessor();
        Pair<Integer, Integer> key = Pair.of(pred.getNodeNumber(), succ.getNodeNumber());

        if(ImpactedHelper.getInstance().cfa_deleted_edges.containsKey(key)) {
            //edge = extractOldEdge(edge);
        }
        //updateIV(succ.impactedVariables, edge.getEdgeType());
        switch (edge.getEdgeType()) {
            case AssumeEdge:
                //updateAssumeEdge(edge);
                checkArgument(edge instanceof CAssumeEdge);
                ((CAssumeEdge)edge).isImpacted = true;
                break;
            case FunctionCallEdge:
                break;
            case StatementEdge: {
                decideIVonStatementEdge((CStatementEdge) edge, succ);
            }
            break;
            case DeclarationEdge:
                break;
            case FunctionReturnEdge:
                break;
            case BlankEdge:
                break;
            case MultiEdge:
                break;
            case ReturnStatementEdge:
                break;
            case CallToReturnEdge:
                //TODO qianshan: not precise, we should analyze the parameters
                //such as, ldv_initialize();
                break;
                //throw new UnsupportedOperationException();
            case UnknownEdge:
            default:
                throw new ClassCastException();
        }
    }

    private static boolean isIfNode(CFANode node) {
        if(node.getNumLeavingEdges() > 0 && node.getLeavingEdge(0).getEdgeType() == CFAEdgeType.AssumeEdge) {
            return true;
        }
        return false;
    }

    private static boolean isAdded(CFAEdge edge) {
        // handle added edges
        CFANode pred = edge.getPredecessor();
        CFANode succ = edge.getSuccessor();
        Pair<Integer, Integer> key = Pair.of(pred.getNodeNumber(), succ.getNodeNumber());
        return ImpactedHelper.getInstance().cfa_added_edges.containsKey(key);
    }

    private static boolean isModified(CFAEdge edge) {
        //handle modified edges
        CFANode pred = edge.getPredecessor();
        CFANode succ = edge.getSuccessor();
        Pair<Integer, Integer> key = Pair.of(pred.getNodeNumber(), succ.getNodeNumber());
        return ImpactedHelper.getInstance().cfa_modified_edges.containsKey(key);
    }

    private static SimpleEdge getOriginalEdge(CFAEdge edge) {
        if(!isModified(edge)) return null;
        CFANode pred = edge.getPredecessor();
        CFANode succ = edge.getSuccessor();
        Pair<Integer, Integer> key = Pair.of(pred.getNodeNumber(), succ.getNodeNumber());
        return ImpactedHelper.getInstance().cfa_modified_edges.get(key).getFirst();
    }

    private static boolean isTrivialChange(SimpleEdge oriEdge, CFAEdge edge){
        if(oriEdge == null)
            return false;
        return false;
    }

    public static void decideIVonStatementEdge(CStatementEdge edge, CFANode node) {
        // such like, x = y + 1
        CStatement stmt = edge.getStatement();
        if(stmt instanceof CFunctionCallStatement) {
            // such like, system_call(x, 1);
            decideIVonFunctionCallEdge(edge, node);
            return;
        }
        if(stmt instanceof CExpressionStatement) {
            // such like, x;
            return;
        }
        checkArgument(stmt instanceof CExpressionAssignmentStatement ||
            stmt instanceof CFunctionCallAssignmentStatement);
        CExpression tmpLeft;
        if(stmt instanceof CExpressionAssignmentStatement)
            tmpLeft = ((CExpressionAssignmentStatement) stmt).getLeftHandSide();
        else if(stmt instanceof CFunctionCallAssignmentStatement)
            tmpLeft = ((CFunctionCallAssignmentStatement) stmt).getLeftHandSide();
        else
            throw new ClassCastException();

        CSimpleDeclaration lvd;
        //CExpression left = ImpactedHelper.getInstance().getProperLeftHand(tmpLeft);
        //qianshan bug fix: *(data + 3UL)
        lvd = ImpactedTransferRelation.getIV(tmpLeft, true);

        checkArgument(lvd != null);
        node.impactedVariables.add(lvd);
        int curImpactedNum = node.impactedVariables.size();
        if (curImpactedNum > ImpactedHelper.getInstance().maxImpactedNum) {
            ImpactedHelper.getInstance().maxImpactedNum = curImpactedNum;
        }
        ImpactedHelper.getInstance().isCurImpacted = false;
    }

    private static void decideIVonFunctionCallEdge(CStatementEdge edge, CFANode node) {
        // such like  system_call(x, 1);
        CStatement stmt = edge.getStatement();
        checkArgument(stmt instanceof CFunctionCallStatement);
        List<CExpression> paras = ((CFunctionCallStatement) stmt).getFunctionCallExpression().getParameterExpressions();
        if(paras.size() == 0) return;
        for(CExpression para : paras) {
            //TODO qianshan handle global variables
            //TODO needn't be implemented?
            // addIfGlobalVar(para, node)
        }
    }
}
