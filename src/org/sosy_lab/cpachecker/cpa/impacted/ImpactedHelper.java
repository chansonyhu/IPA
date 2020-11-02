package org.sosy_lab.cpachecker.cpa.impacted;

import com.google.common.base.Preconditions;
import com.google.common.collect.Sets;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import io.protostuff.parser.Field.Bool;
import java.io.FileNotFoundException;
import java.io.IOException;
import org.sosy_lab.common.Pair;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.common.io.Path;
import org.sosy_lab.common.io.Paths;
import org.sosy_lab.cpachecker.cfa.ast.c.*;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.CoreComponentsFactory;
import org.sosy_lab.cpachecker.core.algorithm.CEGARAlgorithm;
import org.sosy_lab.cpachecker.core.algorithm.invariants.InvariantGenerator;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.reachedset.PartitionedReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractionRefinementStrategy.PredicateSharing;
import org.sosy_lab.cpachecker.cpa.predicate.PredicatePrecision;
import org.sosy_lab.cpachecker.exceptions.SolverException;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.*;
//import org.sosy_lab.cpachecker.util.predicates.interfaces.basicimpl.BooleanFormulaImpl;
import org.sosy_lab.cpachecker.util.predicates.interfaces.basicimpl.AbstractBaseFormulaManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.basicimpl.BooleanFormulaImpl;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.QuantifiedFormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.*;

import javax.annotation.Nullable;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

@Options(prefix="cpa.impacted")
public class ImpactedHelper {
    private static ImpactedHelper instance;
    public final Set<String> globalInitializedVariables = Sets.newHashSet();
    public FormulaManager mgr = null;
    public BooleanFormulaManager bmgr;
    protected FunctionFormulaManager fmgr;
    protected NumeralFormulaManager<NumeralFormula.IntegerFormula, NumeralFormula.IntegerFormula> imgr;
    private UnsafeFormulaManager umgr;
    protected @Nullable NumeralFormulaManager<NumeralFormula, NumeralFormula.RationalFormula> rmgr;
    protected @Nullable BitvectorFormulaManager bvmgr;
    private  @Nullable QuantifiedFormulaManager qmgr;
    protected @Nullable ArrayFormulaManager amgr;
    public CoreComponentsFactory factory;
    public PredicateSharing predicateSharing;
    public InvariantGenerator invariantGenerator;
    public int initialReachedSize = 0;

    public boolean dpllDanger = false;
    boolean isOmitMatching = true;

    public static boolean jsonIO = false;

    static public Set<CVariableDeclaration> inpactedGlobalInitializedVariables = new HashSet<>();

    public Map<Pair<Integer, String>, AbstractState> lastVFileInvariants = new HashMap<>();
    public Map<Integer, Pair> lastVFileDisjInvariants = new HashMap<>();

    public ArrayList<Integer> impactedLines = new ArrayList<>();
    public boolean isCurImpacted = false;
    public static boolean debug_canUseUnpreciseDiff = false;
    public int maxImpactedNum = 0;
    public int maxImpactedNumWhenCPA = 0;
    public boolean isCheckingCEX = false;
    public PredicatePrecision funcWidePrecision = null;
    public boolean isRestart = false;

    public int omits = 0;

    @Option(secure = true, description = "using external cfa diff for precise results",
            name = "diff.external")
    public boolean externalDiff = true;

    @Option(secure = true, description = "using ParallelGZIPOutputStream",
        name = "parallel.output")
    boolean parallelOutput = true;

    @Option(secure = true, description = "using GZIPInputStream/GZIPOutputStream",
        name = "compress.io")
    boolean compressIO = true;

    @Option(secure = true, description = "function wide precision",
        name = "predicate.functionWide")
    public boolean isFunctionWide = false;

    @Option(secure = true, description = "for debug, assume that we have the same revisions",
        name = "isCfaSame")
    boolean isCfaSame = false;

    @Option(secure = true, description = "extract initial precision from previous annotation",
        name = "extractInitialPrec")
    public boolean extractInitialPrec = false;

    @Option(secure = true, description = "",
        name = "eliminate")
    public boolean isEliminate = false;

    @Option(secure = true, description = "",
        name = "aggressive.pathformula")
    public boolean aggressive_pathformula = false;

    @Option(secure = true, description = "invariants as disjunction formula",
            name = "invariants.disjunction")
    public boolean isInvDisj = true;

    private boolean isInputValid = true;
    @Option(secure = true, description = "how to weaken assertion formual",
            name = "weaken.qe")
    public boolean isQEliminate = false;
    static public boolean isHit = false;
    static public int partialHits = 0;
    static public int hits = 0;
    static public int trys = 0;
    static public int bots = 0;
    static public int lastInvs = 0;
    static public int nonvalids = 0;

    public HashMap<Integer, Integer> cfa_newID2oldID = new HashMap<>();
    public HashMap<Integer, Integer> cfa_oldID2newID = new HashMap<>();
    public HashMap<Pair<Integer, Integer>, SimpleEdge> cfa_added_edges = new HashMap<>();
    public HashMap<Pair<Integer, Integer>, SimpleEdge> cfa_deleted_edges = new HashMap<>();
    public HashMap<Pair<Integer, Integer>, Pair<SimpleEdge, SimpleEdge>> cfa_modified_edges =
        new HashMap<>();
    public int doAbstractionNodeCount = 0;
    public HashSet<Integer> doAbstractionNodeNum = new HashSet<Integer>();
    public HashMap<Integer, Set<CSimpleDeclaration>> cfa2iv = new HashMap<>();
    public boolean isFixed = true;
    public boolean readyForAnalysis = false;
    public PredicatePrecision bestPrecisionPerFunction = new PredicatePrecision();

    public Set<CSimpleDeclaration> curImpactedVariables = new HashSet<>();
    public Map<String, FunctionEntryNode> allFunctionNames = new HashMap<>();
    private Map<Pair<String, String>, CFieldDeclaration> cachedFieldDeclarartions =
        new HashMap<>();

    public Path cfaInfoPath;

    @Option(secure = true, description = "file for exporting final loop invariants",
            name = "pre_invariants.file")
    @FileOption(FileOption.Type.OUTPUT_FILE)
    //private Path invariantsFile = Paths.get("./newversion/sourcecode/CPAChecker/output/pre-impacted-invariants.txt");
    public Path invariantsFile = Paths.get("null.txt");

    private ImpactedHelper(Configuration pConfig) {

        try {
            pConfig.inject(this, ImpactedHelper.class);

        } catch (InvalidConfigurationException e) {
            isInputValid = false;
        }
        if(isQEliminate)
            isEliminate = true;
//        CPAMain.invariantInputPath = invariantsFile.toString();
//        if(CPAMain.isReuseInvariant && CPAMain.invariantInputPath != null) {
//            InvariantsReader.loadInvariantFromFile(invariantsFile.toFile());
//        }
    }

    public void loadInvariantFromFile() throws IOException {
        if(isInputValid) {
            try {
                if (invariantsFile.toString().contains("null.txt"))
                    return;
            } catch (NullPointerException npe) {
                return;
            }
            if(CPAMain.isDebug && !invariantsFile.toFile().exists()) {
                throw new FileNotFoundException();
            }
            InvariantsReader.loadInvariantFromFileSimple(invariantsFile.toFile());
        }
    }

    public boolean checkImpacted(AbstractionFormula absF) {
        if(ImpactedHelper.getInstance().isCfaSame) {
            return false;
        }
        for(CSimpleDeclaration sd : ImpactedHelper.getInstance().curImpactedVariables) {
            String iv = sd.getQualifiedName();
            //PredicateAbstractState pS = (PredicateAbstractState) ImpactedHelper.lastVFileInvariants.get(key);
            PathFormula pathFormula = absF.getBlockFormula();
            if(pathFormula.getFormula().toString().contains(iv) || absF.asFormula().toString().contains(iv)) {
                return true;
            }
            if(absF.isTrue()) {
                return true;
            }
        }
        return false;
    }

    public CExpression getProperLeftHand(CExpression exp) throws ClassCastException {
        CExpression result = exp;
        while(!(result instanceof CIdExpression)) {
            if(result instanceof CCastExpression) {
                result = ((CCastExpression) result).getOperand();
            } else if(result instanceof CArraySubscriptExpression) {
                result = ((CArraySubscriptExpression) result).getArrayExpression();
            } else if(result instanceof CFieldReference) {
                //return result;
                result = ((CFieldReference) result).getFieldOwner();
            } else if(result instanceof CBinaryExpression) {
                //TODO qianshan we cannot handle "(ar7_parts + 1UL)->name", in which we shouldn't return null..
                return result;
            } else if(result instanceof CUnaryExpression) {
                // ~set, &addr ...
                result = ((CUnaryExpression) result).getOperand();
            } else  if(result instanceof CPointerExpression) {
                result = ((CPointerExpression) result).getOperand();
            } else if(result instanceof CIntegerLiteralExpression) {
                return null;
            } else if(result instanceof CStringLiteralExpression) {
                return null;
            } else if(result instanceof CCharLiteralExpression) {

            } else {
                System.out.println("UnsupportedExpression:" + result.getClass());
                throw new ClassCastException();
            }
        }
        return result;
    }

    public CFieldReference getProperField(CFieldReference exp) throws ClassCastException {
        return exp;
    }

    public BooleanFormula eliminate0(BooleanFormula formula) throws ClassNotFoundException {
        return formula;
    }

    public Pair<Boolean, BooleanFormula> eliminate(BooleanFormula formula) throws ClassNotFoundException {
        if(!isEliminate)
            return Pair.of(false, formula);
        boolean flag = false;
        SmtInterpolInterpolatingProver smtipP = new SmtInterpolInterpolatingProver((SmtInterpolFormulaManager) mgr);
        //SmtInterpolBooleanFormulaManager bmgr = GlobalInfo.getInstance().getSmtInterpolBooleanFormulaManager();
        BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
        ApplicationTerm f = (ApplicationTerm) (((AbstractBaseFormulaManager) bmgr)).extractInfo(formula);
        //Another way: ((BooleanFormulaImpl)formula).getFormulaInfo();

        String type = f.getFunction().getName();

        if(!type.equals("and")) {
            // System.out.println("Unsupported formula type: " + type + "; " + formula.toString());
            return Pair.of(flag, formula);
        }

        checkArgument(type.equals("and"));

        Term[] terms = f.getParameters();
        HashSet<BooleanFormula> booleanTerms = new HashSet<>();

        BooleanFormula booleanTerm;
        ArrayList<Term> tmpNewTerms = new ArrayList<>();
        for(Term t : terms) {
            if(!isTermImpacted(t)) {
                booleanTerm = ((SmtInterpolFormulaManager) mgr).encapsulateBooleanFormula(t);
                booleanTerms.add(booleanTerm);
                tmpNewTerms.add(t);
            } else {
                flag = true;
            }
        }
        //if(true)
        //    return booleanTerms.isEmpty() ? bmgr.makeBoolean(true) : bmgr.and(booleanTerms);

        //int newTermsSize = tmpNewTerms.size() < 2 ? 2 : tmpNewTerms.size();
        int newTermsSize = tmpNewTerms.size();
        if(newTermsSize == 0) {
            return Pair.of(true, null);
        }
        Term[] newTerms = new Term[newTermsSize];
        //new ApplicationTerm(f.getFunction(), tmpNewTerms.toArray(newTerms), 84937);
//        Set<String> tStrings = new HashSet<>();
//        for(Term t : tmpNewTerms) {
//            String tStr = t.toString();
//            tStrings.add(tStr);
//        }
        int i;
        for(i = 0; i < newTerms.length; i++) {
            newTerms[i] = tmpNewTerms.get(i);
            if(tmpNewTerms.size() < 2)
                break;
        }

        //if(i == 0) {
            //newTerms[i+1] = ((SmtInterpolBooleanFormulaManager) bmgr).getTheory().mTrue;
        //    newTerms[i+1] = tmpNewTerms.get(i);
        //}

        //ApplicationTerm newTerm0 = (ApplicationTerm) smtipP.buildConjunctionOfNamedTerms(tStrings);

        //ApplicationTerm newTerm = (ApplicationTerm) ((SmtInterpolUnsafeFormulaManager) umgr).replaceArgs(f, tmpNewTerms);

        //((SmtInterpolUnsafeFormulaManager) umgr).getFormulaCreator().makeVariable();
        ApplicationTerm new_f;
        if(newTerms.length >= 2) {
            final int hash = ApplicationTerm.hashApplication(f.getFunction(), newTerms);
            new_f = new ApplicationTerm(f.getFunction(), newTerms, hash);
        } else {
            new_f = (ApplicationTerm) newTerms[0];
            //throw new UnsupportedOperationException();
        }
        //((SmtInterpolFormulaManager) mgr).encapsulateBooleanFormula(new_f);
        //return new BooleanFormulaImpl<>(new_f);
        return Pair.of(flag, ((SmtInterpolFormulaManager) mgr).encapsulateBooleanFormula(new_f));
    }

    private boolean isTermImpacted(Term term) {
        String tStr = term.toString();
        for(CSimpleDeclaration sd : ImpactedHelper.getInstance().curImpactedVariables) {
            String iv = sd.getQualifiedName();
            if(tStr.contains(iv)) {
                return true;
            }
        }
        return false;
    }

    public BooleanFormula QEliminate(BooleanFormula formula) {
        if(!isQEliminate)
            return formula;
        BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
        ApplicationTerm f = (ApplicationTerm) (((AbstractBaseFormulaManager) bmgr)).extractInfo(formula);
        //Another way: ((BooleanFormulaImpl)formula).getFormulaInfo();

        String type = f.getFunction().getName();
        checkArgument(type.equals("and"));
        Term[] terms = f.getParameters();
        List<Formula> irrelevantVariables = new ArrayList<>();

        BooleanFormula booleanTerm;
        for(Term t : terms) {
            if(isTermImpacted(t)) {
                booleanTerm = ((SmtInterpolFormulaManager) mgr).encapsulateBooleanFormula(t);
                irrelevantVariables.add(booleanTerm);
            }
        }

        Preconditions.checkNotNull(formula);

        BooleanFormula eliminationResult = formula;
        FormulaManagerView fmv = GlobalInfo.getInstance().getFormulaManagerView();

        if (!irrelevantVariables.isEmpty()) {
            QuantifiedFormulaManagerView qfmgr = fmv.getQuantifiedFormulaManager();
            BooleanFormula quantifiedFormula = qfmgr.exists(irrelevantVariables, formula);
            try {
                eliminationResult = qfmgr.eliminateQuantifiers(quantifiedFormula);
            } catch (InterruptedException ie) {
                ie.printStackTrace();
            } catch (SolverException se) {
                System.out.println("quantifier elimination error");
                se.printStackTrace();
            }
        }

        eliminationResult = fmv.simplify(eliminationResult);
        return eliminationResult;
    }

    public static ImpactedHelper getInstance() {
        if(instance == null) {
            instance = new ImpactedHelper(CPAMain.cpaConfig);
        }
        return instance;
    }

    public void setManagers() {
        mgr = GlobalInfo.getInstance().getFormulaManager();
        bmgr = mgr.getBooleanFormulaManager();
        fmgr = mgr.getFunctionFormulaManager();
        imgr = mgr.getIntegerFormulaManager();
        umgr = mgr.getUnsafeFormulaManager();
        try {
            rmgr = mgr.getRationalFormulaManager();
        } catch (UnsupportedOperationException e) {
            rmgr = null;
        }
        try {
            bvmgr = mgr.getBitvectorFormulaManager();
        } catch (UnsupportedOperationException e) {
            bvmgr = null;
        }
        try {
            qmgr = mgr.getQuantifiedFormulaManager();
        } catch (UnsupportedOperationException e) {
            qmgr = null;
        }
        try {
            amgr = mgr.getArrayFormulaManager();
        } catch (UnsupportedOperationException e) {
            amgr = null;
        }
    }

    public CFieldDeclaration getFieldDeclaration(CFieldReference ref) {

        //TODO qianshan bug fix: (ar7_parts + 1UL)->name, where ar7_parts is a struct
        String value = ref.toString();
        CExpression tmp = ImpactedHelper.getInstance().getProperLeftHand(ref);

        if(tmp instanceof CFieldReference) {
            tmp = ((CFieldReference) tmp).getFieldOwner();
        }

        //TODO qianshan we should uncomment this line later
        checkArgument(tmp instanceof CIdExpression || tmp == null  || tmp instanceof CBinaryExpression);
        if(tmp instanceof CBinaryExpression) {
            tmp = ((CBinaryExpression) tmp).getOperand1();
        }
        CSimpleDeclaration declaration;
        if(tmp == null && ref.getFieldOwner() instanceof CBinaryExpression){
            checkArgument(((CBinaryExpression) ref.getFieldOwner()).getOperand1() instanceof CIdExpression);
            CIdExpression exp = (CIdExpression) ((CBinaryExpression) ref.getFieldOwner()).getOperand1();
            declaration = exp.getDeclaration();
        } else {
            if(tmp instanceof CFieldReference)
                tmp = ((CFieldReference) tmp).getFieldOwner();
            declaration = ((CIdExpression) tmp).getDeclaration();
        }
        Map<Pair<String, String>, CFieldDeclaration> cachedFieldDeclarartions =
            ImpactedHelper.getInstance().cachedFieldDeclarartions;
        Pair<String, String> key = Pair.of(value, declaration.getQualifiedName());
        if(cachedFieldDeclarartions.containsKey(key))
            return cachedFieldDeclarartions.get(key);
        else {
            CFieldDeclaration newAddedDecl = new CFieldDeclaration(declaration, value);
            cachedFieldDeclarartions.put(key, newAddedDecl);
            return newAddedDecl;
        }
    }

}
