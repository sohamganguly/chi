package org.jmlspecs.openjml.jmltest;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.IArithmeticMode;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Nowarns;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.Utils.JmlNotImplementedException;
import org.jmlspecs.openjml.esc.BiMap;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.esc.Label;
import org.jmlspecs.openjml.esc.JmlAssertionAdder.NoModelMethod;
import org.jmlspecs.openjml.ext.Arithmetic;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlType;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAssert;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCIf;
import com.sun.tools.javac.tree.JCTree.JCLabeledStatement;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.Position;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class JmlTestAssertionAdder extends JmlTestTreeScanner{
    
    protected java.util.Map<Symbol,Symbol> localVariables = new java.util.HashMap<Symbol,Symbol>();
    
// Parameters of this instance of JmlAssertionAdder 
    
    /** If true then every part of every AST is copied; if false then items
     * expected to be immutable such as JCLiteral, qualified ids (in import
     * statements, static type designators), JCAnnotation are not duplicated. 
     * Non-AST objects
     * such as Type, Token or JmlToken values are not duplicated in any case.
     */
    public boolean fullTranslation = true;
    
    // NOTE: We support !esc || !rac but not esc && rac.
    //@ invariant !esc || !rac;
    
    /** True if we are translating for static checks */
    public boolean esc ;
    
    /** True if we are translating for RAC */
    public boolean rac ;
    
    /** If true, we are making a pure copy (!esc && !rac)*/
    public boolean pureCopy;
    
    /** If true, then error messages in generated RAC code include source
     * code snippets with the customary textual ^ pointers to error locations.
     * This adds bulk to the RAC-ed program, though I've not measured whether
     * it is significant. The field is initialized from a user option and not meant
     * to be set externally.
     */
    protected boolean showRacSource;
    
    /** If true, then in the RAC translation, assume statements and assumptions
     * implied by JML are checked as if they were assert statements.
     * The field is initialized from a user option and not meant to be set
     * externally.
     */
    protected boolean racCheckAssumeStatements;

    /** If true, then explicit checks are included even when the Java
     * language would catch the error itself (e.g., OpenJML will check for a
     * null reference in advance of a dereference and Java throwing a 
     * NullPointerException). This should always be true for esc, but only
     * true for rac if the appropriate option is set.
     */
    public boolean javaChecks;
    
    // Constant items set in the constructor
    
    /** The compilation context */
    final protected Context context;
    
    /** Cached value of the Log tool */
    final public Log log;
    
    /** Cached value of the specs database */
    final protected JmlSpecs specs;
    
    /** Cached value of JmlTypes */
    final public JmlTypes jmltypes;
    
    /** Cached value of the AST node factory */
    final public JmlTree.Maker M;
    
    /** Cached value of the names table */
    final public Names names;
    
    /** Cached value of the symbol table */
    final public Symtab syms;
    
    /** Cached value of the Types tool */
    final public Types types;
    
    /** Cached value of the Utils tool */
    final public Utils utils;
    
    /** Cached value of the Nowarns object */
    final protected Nowarns nowarns;
    
    /** Cached value of the Attribute tool */
    final protected JmlAttr attr;
    
    /** The JmlTreeUtils object, holding a bunch of tree-making utilities */
    final public JmlTreeUtils treeutils;
    
    /** The tool to find class symbols */
    final protected ClassReader reader;
    
    /** The symbol for the runtime Utils class */
    final protected ClassSymbol utilsClass;

    /** The Name used for the result of a method */
    final protected Name resultName;
    
    /** The symbol for the variable that holds the result of a method */
    protected Symbol resultSym = null;
    
    /** An expression to be used for \result when translating postconditions;
     * the expression should always be copied afresh for each instantiation */
    protected JCExpression resultExpr = null;
    
    /** The Name used for exceptions thrown in the body of a method */
    final protected Name exceptionName;
    
    /** The symbol for the variable that tracks exceptions in the body of a method */
    protected Symbol exceptionSym = null;
    
    /** The symbol for the variable that holds allocation ids to distinguish dynamically allocated objects */
    protected Symbol allocSym = null;
    
    /** The symbol for the variable that says whether an object is allocated */
    protected Symbol isAllocSym = null;
    
    /** A counter used to make distinct ids for newly allocated Objects */
    protected int allocCounter = 0;
    
    /** Exception Symbols used for various methods */
    protected Map<JCMethodDecl,Symbol> exceptionSymbols = new HashMap<JCMethodDecl,Symbol>();
    
    /** The Name used for catching exceptions thrown by called methods */
    final protected Name exceptionNameCall;
    
    /** The Name used for holding the location at which the final return or throw statement occurs */
    final protected Name terminationName;
    
    /** The symbol to go with terminationName. */
    protected Symbol terminationSym = null;

    /** Termination Symbols used for various methods */
    protected Map<JCMethodDecl,Symbol> terminationSymbols = new HashMap<JCMethodDecl,Symbol>();
    
    // Fields used and modified during translation
    // These should only be modified by visit methods
    
    /** The AST being processed when in a sub-tree of a method declaration */
    protected JmlMethodDecl methodDecl = null;
    
    /** The parent class of the method being converted, for use while the
     * declarations of the class are being walked, and while a method is
     * being translated stand-alone (without having been reached by walking
     * the tree from above).
     */
    protected JmlClassDecl classDecl = null;
    
    /** The Ident to use when translating this - starts as the this for the
     * receiver object, but can change as methods or constructors are called.
     */
    protected JCIdent currentThisId;

    /** The receiver expression, such as when performing a method call within the body of the method being translated.
     */
    protected JCExpression currentThisExpr;
    
    protected Symbol enclosingMethod;
    protected Symbol enclosingClass;
    
    /** The mode to use to model arithmetic operations - only null until initialized */
    protected IArithmeticMode currentArithmeticMode = null;
    
    /** Depth of nesting of applyHelper calls */
    protected int applyNesting;
    
    /** The counter used to make uniquely named variables for preconditions,
     * unique within a method body. */
    int precount = 0;
    
    /** The counter used to make uniquely named variables for assertions,
     * unique within a method body. */
    protected int assertCount = 0;
    
    /** A counter that ensures unique variable names (within a method body). */
    protected int count = 0;
    
    /** A map from formal parameter to actual argument, used when translating
     * methods called within a method body; also used to map formals in inherited
     * method specs to actual arguments or to the formals in the base method.
     */
    protected Map<Object,JCExpression> paramActuals;
    
    /** A map from formals to a declaration of a variable that holds the formal's
     * value at method body entrance (for use by postconditions).
     */
    protected Map<Symbol,JCVariableDecl> preparams = new HashMap<Symbol,JCVariableDecl>();
    
    /** A map from specification case to a JCIdent that is a variable holding
     * the value of the precondition for that specification case.
     */
    protected Map<JmlSpecificationCase,JCIdent> preconditions = new HashMap<JmlSpecificationCase,JCIdent>();
    
    /** A map from old nodes to new ones, for use when there are node references
     * (rather than copies of trees) within an AST. In particular used to 
     * set the target fields for break and continue statements.
     */
    protected java.util.Map<JCTree,JCTree> treeMap = new HashMap<JCTree,JCTree>();
    
    /** A List used to accumulate translated definitions of a class, for cases
     * where new declarations are needed.
     */
    protected ListBuffer<JCTree> classDefs = null;
    
    /** A list to collect statements as they are being generated. */
    protected ListBuffer<JCStatement> currentStatements;

    /** A list aliased with the place to put computations of \pre expressions. */
    protected ListBuffer<JCStatement> oldStatements;

    /** The prelude statements of the current method */
    protected ListBuffer<JCStatement> initialStatements;
    
    /** A stack of 'currentStatements' . The current value of 'currentStatements'
     * is NOT on this stack. */
    protected LinkedList<ListBuffer<JCStatement>> statementStack = new LinkedList<ListBuffer<JCStatement>>();

    /** A stack of labeled statements that might be targets of continue statements */
    java.util.Stack<JCLabeledStatement> continueStack = new java.util.Stack<JCLabeledStatement>();

    /** Stack of the synthetic index (trip count) variables for loops enclosing
     * the code under current consideration. 0th element is the currently innermost scope
     */
    protected java.util.List<JCVariableDecl> indexStack = new LinkedList<JCVariableDecl>();
    
    /** true when translating JML constructs, false when translating Java constructs.
     * This is set and manipulated by the visitor methods 
     */
    public boolean translatingJML = false;
    public boolean splitExpressions = true;
    public boolean convertingAssignable = false;
    public boolean assumingPureMethod = false;
    
    /** Contains an expression that is used as a guard in determining whether expressions
     * are well-defined. For example, suppose we are translating the expression 
     * a != null && a[i] == 0. Then condition is 'true' when a!=null is translated.
     * But when a[i] is translated, 'condition' will be a != null. The well-definedness
     * check for a[i] will then be (a != null) ==> (a != null && i >= 0 && i < a.length).
     * So the full expression is well-defined only if that implication can be proved given 
     * other pre-conditions.
     */
    public JCExpression condition;
    
    // FIXME - dcoument
    protected java.util.List<JmlStatementExpr> wellDefinedConditions = new java.util.LinkedList<JmlStatementExpr>();
    
    /** Set to true when we are translating a normal or exceptional postcondition. It is used
     * to be sure the correct scope is used when method parameters are used in the postcondition.
     * If a method parameter is used in a postcondition it is evaluated in the pre-state since
     * any changes to the parameter within the body of the method are discarded upon exit and
     * are invisible outside the method (i.e. in the postcondition).
     */
    protected boolean isPostcondition;
    
    /** Used to note the environment (i.e., \old label) under which we are currently
     * evaluating; null indicates the current state; an empty string indicates
     * the pre-state, otherwise it is the JCIdent of the label in the \old statement
     */
    @Nullable protected JCIdent oldenv;
    
    /** The \old label to use for the pre-state */
    protected JCIdent preLabel;
    
    /** Used to hold the result of non-expression AST nodes */
    protected JCTree result;
    
    /** Used to hold the result of expression AST nodes, so equal to 'result'
     * when 'result' is a JCExpression. */
    protected JCExpression eresult;
    
    protected JCBlock axiomBlock = null;
    
    /** Assertions that can be changed to be feasibility checks */
    public Map<Symbol,java.util.List<JCTree.JCParens>> assumptionChecks = new HashMap<Symbol,java.util.List<JCTree.JCParens>>();
    public Map<Symbol,java.util.List<JmlTree.JmlStatementExpr>> assumptionCheckStats = new HashMap<Symbol,java.util.List<JmlTree.JmlStatementExpr>>();
    
    // FIXME - review which of these bimaps is actually needed
    
    /** A bi-map used to record the mapping between original and rewritten nodes, for reporting expression values */
    public BiMap<JCTree, JCTree> exprBiMap = new BiMap<JCTree, JCTree>();
    
    /** A bi-map used to record statement mappings for reporting counterexample paths */
    public BiMap<JCTree,JCTree> pathMap = new BiMap<JCTree,JCTree>();
    
    /** A bi-map used to record the mapping between original and rewritten method ASTs */
    public BiMap<JmlMethodDecl, JmlMethodDecl> methodBiMap = new BiMap<JmlMethodDecl, JmlMethodDecl>();

    /** A bi-map used to record the mapping between original and rewritten class ASTs */
    public BiMap<JmlClassDecl, JmlClassDecl> classBiMap = new BiMap<JmlClassDecl, JmlClassDecl>();

    /** A map from Class Symbols to an ident containing the this symbol for that class */
    public Map<Symbol,JCIdent> thisIds = new HashMap<Symbol,JCIdent>();
    
    public int assumeCheckCount = 0;
    
    public final static String assumeCheckVar = "__JML_AssumeCheck_";
    
    public VarSymbol assumeCheckSym;
    
    public Map<JmlMethodDecl,java.util.List<JmlStatementExpr>> assumeChecks = new HashMap<JmlMethodDecl,java.util.List<JmlStatementExpr>>();
    
    public int heapCount = 0;
    
    public VarSymbol heapSym = null;
    
    public Name heapVarName;
    
    public Map<Name,Integer> oldHeapValues = new HashMap<>();
    public Map<Name,Map<Symbol,MethodSymbol>> oldHeapMethods = new HashMap<>();
    {
        oldHeapMethods.put(null, new HashMap<Symbol,MethodSymbol>());
    }
    
    public boolean useNamesForHeap = true; // if false, use arguments for heap
    
    public boolean jmltest ;
    
    protected boolean checkAccessEnabled;
    
    JmlAssertionAdder openjmlassertionadder;
    
    public boolean useMethodAxioms;
    
    public JmlTestAssertionAdder(Context context, boolean jmltest) {
        this.context = context;
        this.esc = false;
        this.rac = false;
        this.jmltest = true;
        this.log = Log.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
        this.nowarns = Nowarns.instance(context);
        this.syms = Symtab.instance(context);
        this.types = Types.instance(context);
        this.utils = Utils.instance(context);
        this.specs = JmlSpecs.instance(context);
        this.jmltypes = JmlTypes.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.attr = JmlAttr.instance(context);
        this.resultName = names.fromString(Strings.resultVarString);
        this.exceptionName = names.fromString(Strings.exceptionVarString);
        this.exceptionNameCall = names.fromString(Strings.exceptionCallVarString);
        this.terminationName = names.fromString(Strings.terminationVarString);
        this.reader = ClassReader.instance(context);
        this.reader.init(syms);
        this.utilsClass = reader.enterClass(names.fromString(Strings.runtimeUtilsFQName));
        this.preLabel = treeutils.makeIdent(Position.NOPOS,Strings.empty,syms.intType); // Type does not matter
        this.checkAccessEnabled = JmlOption.isOption(context,JmlOption.CHECK_ACCESSIBLE);
        initialize();
    }
    
    /** Convert method overridden for JmlTest
     * @author soham
     * @param tree
     * @param jmltest
     * @return
     */
    @SuppressWarnings("unchecked")
    public @Nullable <T extends JCTree> T convert(@Nullable T tree, boolean jmltest) {
        if(tree == null) { 
            result = null;
            return null;
        }
        scan(tree, jmltest);
        
        if (localVariables.isEmpty()) exprBiMap.put(tree, result);
        
        return (T)result;
    }
    
    /** Produces a MethodSym for an initialization block; any variables 
     * declared within an initialization block need a 'method' as an owner
     * rather than a class, or they will be interpreted as class fields.
     */
    protected JmlMethodDecl methodSymForInitBlock(DiagnosticPosition pos, long flags, JCClassDecl classDecl) {
        MethodSymbol msym = new MethodSymbol(
                flags, 
                classDecl.name, 
                null, 
                classDecl.sym);
        methodDecl = M.MethodDef(
                M.Modifiers(flags, M.Annotations(List.<com.sun.tools.javac.code.Attribute.Compound>nil())),
                classDecl.name,
                null,
                null,
                null,
                null,
                null,
                null, //body,
                null);
        methodDecl.pos = pos.getPreferredPosition();
        methodDecl.sourcefile = Log.instance(context).currentSourceFile();
        methodDecl.docComment = null;
        methodDecl.cases = null;
        methodDecl.methodSpecsCombined = null;
        methodDecl.sym = msym;
        methodDecl.type = null;
        return methodDecl;
    }
    
    /** Start collecting statements for a new block; push currentStatements 
     * onto a stack for later use */
    protected ListBuffer<JCStatement> pushBlock() {
        ListBuffer<JCStatement> temp = currentStatements;
        statementStack.add(0,currentStatements);
        currentStatements = new ListBuffer<JCStatement>();
        //if (temp != null) System.out.println("PUSHING " + temp.hashCode() + "  NEW " + currentStatements.hashCode());
        return temp;
    }
    
    public java.util.List<Symbol> completedInvariants = new LinkedList<Symbol>();
    public java.util.Set<Symbol> inProcessInvariants = new HashSet<Symbol>();
    Map<TypeSymbol,Type> typevarMapping;
    
    protected void clearInvariants() {
        completedInvariants.clear();
        inProcessInvariants.clear();
    }
    
    protected boolean startInvariants(Symbol csym, DiagnosticPosition pos) {
        if (completedInvariants.contains(csym)) return true; // skip processing
        if (inProcessInvariants.add(csym)) return false; // ok to do processing
        log.error(pos, "jml.recursive.invariants", csym.getQualifiedName());
        MethodSymbol msym = null;
        if (pos instanceof JCMethodInvocation) {
            msym = (MethodSymbol)treeutils.getSym(((JCMethodInvocation)pos).meth);
        } else if (pos instanceof JmlMethodDecl) {
            msym = ((JmlMethodDecl)pos).sym;
        }
        if (msym != null) attr.addHelper(msym);
        return true; // skip processing
    }
    
    /** This generates a JmlExpressionStatement comment statement with the given string as
     * text; the statement is not added to any statement list.
     */
    protected JmlStatementExpr comment(DiagnosticPosition pos, String s, /*@ nullable */JavaFileObject source) {
        if (s.contains("\n") || s.contains("\r")) {
            s = s.replace("\r\n"," ").replace('\r', ' ').replace('\n', ' ');
        }
        JmlStatementExpr st = M.at(pos).JmlExpressionStatement(JmlTokenKind.COMMENT,null,M.at(pos).Literal(s));
        st.associatedSource = source;
        return st;
    }
    
    /** Add a statement at the end of the active currentStatements sequence,
     * returning the argument */ 
    protected <T extends JCStatement> T addStat(T stat) {
        if (currentStatements != null) currentStatements.add(stat);
        else if (classDefs != null) classDefs.add(stat); 
        else log.error(stat.pos,  "jml.internal", "No place to add a statement");
        return stat;
    }
    
    /** Add a statement at the end of the given buffer of statements,
     * returning the statement added */ 
    protected <T extends JCStatement> T addStat(ListBuffer<JCStatement> stats, T stat) {
        stats.add(stat);
        return stat;
    }
    
    protected void addTraceableComment(JCTree t) {
        JCStatement c = openjmlassertionadder.comment(t);
        pathMap.put(t, c);
        addStat(c);
    }
    
    protected void addTraceableComment(JCTree t, String description) {
        addStat(traceableComment(t,t,description,null));
    }

    protected void addTraceableComment(JCTree t, JCExpression expr, String description) {
        addStat(traceableComment(t,expr,description,null));
    }

    protected void addTraceableComment(JCTree t, JCTree expr, String description, String info) {
        addStat(traceableComment(t,expr,description,info));
    }

    /** Create a comment that is used for tracing; the value of the given expression (and subexpressions)
     * is printed as part of the trace.
     * @param t the source location to cite for the comment
     * @param expr the expression to trace
     * @param description the description of the expression to give (typically a string representation of the symbolic expression)
     * @param info additional information to be provided with the comment
     * @return
     */
    protected JCStatement traceableComment(JCTree t, JCTree expr, String description, String info) {
        JavaFileObject source = null;
        if (t instanceof JmlTree.JmlSource) source = ((JmlTree.JmlSource)t).source();
        JmlStatementExpr c = comment(t,description,source);
        c.id = info;
        pathMap.put(expr, c);
        return c;
    }
    
    

    
    
    /** Adds invariants, constraints and initially clauses from a given class and its parents.
     * This is used for pre and post conditions, in which case the invariants from a 
     * meethod's own class (and its parents) are used; it is also used for other 
     * relevant classes, such as the classes of method parameters. The value of
     * 'methodDecl' (and 'classDecl') is the method for which a logical encoding
     * is being constructed, but is not necessarily the callee class which is causing
     * the invariants to be loaded.
     * 
     * @param pos       the code position which occasioned needing the invariants
     * @param isConstructor whether the callee (or the method itself if there is no callee) is a contructor
     * @param isSuper   true if the callee method is a super() call 
     * @param basecsym  the base TypeSymbol from which to take invariants (this may
     *                  or may not be the class containing the methodDecl)
     * @param receiver  the THIS object to use when translating the invariants -
     *                  this is either the receiver for the original method call
     *                  or is the parameter or return value for which invariants
     *                  are being loaded. This parameter is null iff the base method
     *                  is static and not a constructor; if it is a constructor the 
     *                  value is the object being produced by the constructor.
     * @param stats     the statement list into which to add the invariants
     * @param isHelper  whether the callee or base method is a helper method (whichever one the invariants are for)
     * @param prepost   true if we are inserting invariants as pre or post conditions (rather than on behalf of a called procedure)
     * @param isPost    whether we are adding clauses after (post) or before the method
     * @param assume    whether clauses are assumed or asserted
     * @param invariantLabel the cause of needing the invariant
     */
    protected void addInvariants(DiagnosticPosition pos, Type basetype, JCExpression receiver, ListBuffer<JCStatement> stats, boolean prepost, boolean isConstructor, boolean isSuper,
            boolean isHelper, boolean isPost, boolean assume, Label invariantLabel, Object ... invariantDescription) {
        TypeSymbol basecsym = basetype.tsym;
        if (basetype.isPrimitive()) return;
        if (!translatingJML) clearInvariants();
        if (startInvariants(basecsym,pos)) return;
//        System.out.println("STARTING " + basecsym);
        java.util.List<Type> parents = openjmlassertionadder.parents(basetype, true);
//        boolean isConstructedObject = isConstructor && receiver.sym == currentThisId.sym;
        boolean self = basecsym == methodDecl.sym.owner; // true if we are inserting invariants for the base method, either as pre and post conditions or prior to calling a callee
        boolean contextIsStatic = receiver == null; // && !methodDecl.sym.isConstructor(); //|| (self && utils.isJMLStatic(methodDecl.sym));
        
        // Iterate through parent classes and interfaces, assuming relevant axioms and invariants
        // These are checked prior to calling the callee
        ListBuffer<JCStatement> prevStats = currentStatements;
        JCIdent prevThisId = currentThisId;
        JCExpression prevThisExpr = currentThisExpr;
        Map<TypeSymbol,Type> savedTypevarMapping = typevarMapping;
        try {
            ListBuffer<JCStatement> staticStats = stats;
            
//            if (receiver instanceof JCFieldAccess) {
//            // FIXME - not sure about this patch (this branch) - needs testing
//                JCFieldAccess that = (JCFieldAccess)receiver;
//                currentThisExpr = currentThisId = treeutils.makeIdent(that.pos, that.name, that.sym);
//            } else if (receiver == null || receiver instanceof JCIdent) {
              {
                if (receiver instanceof JCIdent) currentThisId = (JCIdent)receiver;
                currentThisExpr = receiver;

                for (Type ctype: parents) {
                    if (!(ctype.tsym instanceof ClassSymbol)) continue;
                    typevarMapping = openjmlassertionadder.typemapping(ctype, null, null);
                    ListBuffer<JCStatement> check = pushBlock();
                    ListBuffer<JCStatement> instanceStats = currentStatements;
                    try {
                        ClassSymbol csym = (ClassSymbol)ctype.tsym;
                        JmlSpecs.TypeSpecs tspecs = specs.get(csym);
                        if (tspecs == null) continue; // FIXME - why might this happen - see racnew.testElemtype & Cloneable

                        if (prepost && !isPost && !methodDecl.sym.isConstructor()) {
                            // Adding in invariant about final fields
                            instanceStats.add(comment(pos,(assume? "Assume" : "Assert") + " final field invariants for " + csym,null));
                            JCExpression conj = null;
                            //JCExpression staticconj = null;
                            for (Symbol s : csym.getEnclosedElements()) {
                                if (s instanceof VarSymbol) {
                                    if (contextIsStatic && !utils.isJMLStatic(s)) continue;
                                    // FIXME - check visibility
                                    VarSymbol v = (VarSymbol)s;
                                    Object o = v.getConstantValue();
                                    if (o != null) {
                                        JCIdent id = treeutils.makeIdent(v.pos,v);
                                        JCLiteral val = treeutils.makeLit(v.pos,v.type,o);
                                        JCExpression e = treeutils.makeEquality(v.pos, id, val);
                                        if (utils.isJMLStatic(s)) {
                                            //staticconj = staticconj == null ? e : treeutils.makeAnd(v.pos, staticconj, e);
                                        } else {
                                            conj = conj == null ? e : treeutils.makeAnd(v.pos, conj, e);
                                        }
                                    }
                                }
                            }
                            if (conj != null) {
                                currentStatements = instanceStats;
                                conj = openjmlassertionadder.convertJML(conj);
                                if (assume) openjmlassertionadder.addAssume(pos,invariantLabel,conj);
                                else  openjmlassertionadder.addAssert(pos,invariantLabel,conj);
                            }
                            //                        if (staticconj != null) {
                            //                            currentStatements = staticStats;
                            //                            staticconj = convertJML(staticconj);
                            //                            if (assume) addAssume(pos,invariantLabel,staticconj);
                            //                            else  addAssert(pos,invariantLabel,staticconj);
                            //                        }
                        }

                        staticStats.add(comment(pos,(assume? "Assume" : "Assert") + " invariants for " + csym,null));
                        // Do the non_null fields
                        // FIXME - not sure that we should exclue rac
                        if (assume && !rac) for (Symbol s : csym.getEnclosedElements()) {
                            if (s instanceof VarSymbol) {
                                if (!utils.visible(classDecl.sym, csym, s.flags()/*, methodDecl.mods.flags*/)) continue;
                                if (!utils.isJMLStatic(s) && contextIsStatic) continue;
                                if (isConstructor && (!assume || basetype == ctype)) continue;
                                VarSymbol v = (VarSymbol)s;
                                Type vartype = v.type;
                                JCExpression field;
                                if (receiver == null) field = treeutils.makeIdent(pos,v);
                                else field = M.at(pos).Select(receiver, v);
                                if (!vartype.isPrimitive()) {
                                    JCExpression e = treeutils.makeNotNull(pos.getStartPosition(),field); // FIXME - position not right
                                    if (specs.isNonNull(v)) {
                                        if (assume) openjmlassertionadder.addAssume(pos,Label.POSSIBLY_NULL_FIELD,
                                                e,
                                                null,null); // FIXME - no associated position?
                                        else  openjmlassertionadder.addAssert(pos,Label.POSSIBLY_NULL_FIELD,
                                                e,
                                                null,null); // FIXME - no associated position?
                                    }
                                    if (assume) {
                                        openjmlassertionadder.addAssume(pos, Label.IMPLICIT_ASSUME, treeutils.makeDynamicTypeInEquality(pos, field, vartype), 
                                                null, null); // FIXME - associated position should be the declaration
                                    }
                                    
                                } else {
                                    // FIXME - range constraints?
                                }
                            }
                        }
                        // Do the actual invariants
                        for (JmlTypeClause clause : tspecs.clauses) {
                            if (!utils.visible(classDecl.sym, csym, clause.modifiers.flags/*, methodDecl.mods.flags*/)) continue;
                            JmlTypeClauseExpr t;
                            DiagnosticPosition cpos = clause;
                            boolean clauseIsStatic = utils.isJMLStatic(clause.modifiers,csym);
                            currentStatements = clauseIsStatic? staticStats : instanceStats;
                            //JavaFileObject prevSource = log.useSource(clause.source());
                            try {
                                // FIXME - guard against the receiver being null for non-static invariants
                                switch (clause.token) {
                                    // invariants on both pre and post for all classes of parameters and return value
                                    // Pre and post conditions:
                                    //      helper - no invariants for class of method
                                    //      non-helper constructor - invariants only on post
                                    //      non-helper method - invariants on pre and post
                                    // Calling a method - caller invariants
                                    //      same as pre and postconditions, except
                                    //      when a constructor is calling super(), no invariants of containing class are assumed in post
                                    // Calling a method - callee invariants
                                    //      callee is helper - no invariants in pre or post for class containing method
                                    //      callee is super() - invariants of super class on post
                                    //      callee is constructor - invariants on post
                                    //      callee is method - invariants on pre and post
                                    case INVARIANT:
                                    {
                                        if (contextIsStatic && !clauseIsStatic) break;
                                        if (isHelper) break;
                                        if (isSuper && !isPost) break;
                                        boolean doit = false;
                                        if (!isConstructor || isPost) doit = true; // pre and postcondition case
                                        if (isConstructor && clauseIsStatic) doit = true;
                                        if (doit) {
                                            t = (JmlTypeClauseExpr)openjmlassertionadder.convertCopy(clause); // FIXME - why copy the clause
                                            addTraceableComment(t.expression,clause.toString());
                                            JCExpression e = openjmlassertionadder.convertJML(t.expression,treeutils.trueLit,isPost);
                                            // FIXME - be nice to record where called from, not just the location of the invariant declaration
                                            if (assume) openjmlassertionadder.addAssume(pos,invariantLabel,
                                                    e,
                                                    cpos,clause.source, invariantDescription);
                                            else  openjmlassertionadder.addAssert(pos,invariantLabel,
                                                    e,
                                                    cpos,clause.source, invariantDescription);
                                            //                                        JavaFileObject source = log.useSource(clause.source);
                                            //                                        if (assume) addAssume(cpos,invariantLabel,
                                            //                                                e,
                                            //                                                cpos,clause.source, invariantDescription);
                                            //                                        else  addAssert(cpos,invariantLabel,
                                            //                                                e,
                                            //                                                invariantDescription);
                                            //                                        log.useSource(source);
                                        }
                                        break;
                                    }
                                    default:
                                        // Skip

                                }
                            } catch (NoModelMethod e) {
//                                log.error(clause.pos, "jml.message", e.getMessage());
                            } catch (JmlNotImplementedException e) {
                                openjmlassertionadder.notImplemented(clause.token.internedName() + " clause containing ", e, clause.source());
                            } finally {
                                //log.useSource(prevSource);
                            }
                        }
                    } finally {
                        currentStatements = instanceStats;
                        JCBlock bl = popBlock(0,pos,check);
                        if (!onlyComments(bl.stats)) {
                            if (contextIsStatic) {
                                staticStats.add(bl);
                            } else {
                                JCExpression ex = treeutils.makeNeqObject(pos.getPreferredPosition(),receiver,treeutils.nullLit);
                                JCStatement st = M.at(pos).If(ex, bl, null);
                                staticStats.add(st);
                            }
                        }
                    }

                }
//            } else {
//                notImplemented(receiver, "receiver of class " + (receiver == null ? "-null-" : receiver.getClass().getName()));
            }
        } finally {
            endInvariants(basecsym);
            if (!translatingJML) clearInvariants();
//            System.out.println("ENDING " + basecsym + " " + inProcessInvariants.contains(basecsym) + " " + completedInvariants.contains(basecsym));
            currentStatements = prevStats;
            currentThisId = prevThisId;
            currentThisExpr = prevThisExpr;
            typevarMapping = savedTypevarMapping;
        }

    }
    
    protected void endInvariants(Symbol csym) {
        inProcessInvariants.remove(csym);
        completedInvariants.add(csym);
    }
    
    /** Wrap the active currentStatements as a block (which is returned) and 
     * then resume collecting statements with currentStatements value on the 
     * top of the stack (which is also removed from the stack) 
     */
    /*protected JCBlock popBlock(long flags, DiagnosticPosition pos) {
        JCBlock b = M.at(pos).Block(flags, currentStatements.toList());
        //System.out.println("POPPING   " + currentStatements.hashCode());
        currentStatements = statementStack.removeFirst();
        return b;
    }*/
    
    protected JCBlock popBlock(long flags, DiagnosticPosition pos, ListBuffer<JCStatement> check) {
        JCBlock b = M.at(pos).Block(flags, currentStatements.toList());
        //System.out.println("POPPING   " + currentStatements.hashCode());
        currentStatements = statementStack.removeFirst();
        if (check != currentStatements) {
            log.error("jml.internal", "MISMATCHED BLOCKS");
        }
        return b;
    }
    
    protected JCBlock checkStaticInitialization() {
        JmlMethodDecl md = methodSymForInitBlock(classDecl, Flags.STATIC, classDecl);

        pushBlock();
        for (Symbol s: classDecl.sym.getEnclosedElements()) {
            if (utils.isJMLStatic(s) && !s.type.isPrimitive() && s instanceof VarSymbol) {
                VarSymbol v = (VarSymbol)s;
                if (specs.isNonNull(v)) {
                    JCIdent id = treeutils.makeIdent(v.pos, v);
                    JCExpression e = treeutils.makeNeqObject(v.pos, id, treeutils.nullLit);
                    //e = convertJML(e);
                    JCStatement st = openjmlassertionadder.addAssert(new JCDiagnostic.SimpleDiagnosticPosition(v.pos),Label.STATIC_INIT,e,"non-null static field has null value: " + v.name);
                    if (st instanceof JCAssert) {
                        e = ((JCAssert)st).cond;
                    } else if (st instanceof JCIf) {
                        e = ((JCIf)st).cond;
                        if (e instanceof JCUnary) e = ((JCUnary)e).arg;
                    } else {
                        e = null;
                    }
                    if (e instanceof JCIdent) {
                        ((JCIdent)e).sym.owner = md.sym;
                    }
                    
                }
            }
        }
        // FIXME - what are the rules about accessibility for static initializers
        boolean pv = checkAccessEnabled;
        checkAccessEnabled = false;
        try {
             addInvariants(classDecl,classDecl.sym.type,null,currentStatements,true,false,false,false,true,false,Label.STATIC_INIT,
                "invariant is false");
        } finally {
            checkAccessEnabled = pv;
        }
        JCBlock bl = popBlock(Flags.STATIC,classDecl);
        if (onlyComments(bl.stats)) bl = null;
        return bl;
    }
    
    /** Wrap the active currentStatements as a block (which is returned) and 
     * then resume collecting statements with currentStatements value on the 
     * top of the stack (which is also removed from the stack) 
     */
    protected JCBlock popBlock(long flags, DiagnosticPosition pos) {
        JCBlock b = M.at(pos).Block(flags, currentStatements.toList());
        //System.out.println("POPPING   " + currentStatements.hashCode());
        currentStatements = statementStack.removeFirst();
        return b;
    }
    
    /** Returns true iff the only statements on the list are comment statements */
    protected boolean onlyComments(Iterable<JCStatement> list) {
        for (JCStatement s: list) {
            if (!(s instanceof JmlStatementExpr && ((JmlStatementExpr)s).token == JmlTokenKind.COMMENT)) return false;
        }
        return true;
    }
    
    
    
    public JCIdent makeThisId(int pos, Symbol sym)  {
        VarSymbol THISSym = treeutils.makeVarSymbol(Flags.STATIC,names.fromString(Strings.thisName),sym.type, Position.NOPOS);
        THISSym.owner = esc ? null : sym; 
            // In esc, the owner is null (instead of sym) to indicate
            // that this new symbol is a synthetic variable that will not ever
            // be assigned to.
        JCIdent id = treeutils.makeIdent(pos,THISSym);
        this.thisIds.put(sym, id);
        exprBiMap.put(id,id);
        return id;
    }
    
    public void visitJmlClassDecl (JmlClassDecl that, boolean jmltest) {
        Main.instance(context).pushOptions(that.mods);
        
        JmlMethodDecl savedMethodDecl = this.methodDecl;
        JmlClassDecl savedClassDecl = this.classDecl;
        ListBuffer<JCTree> savedClassDefs = this.classDefs;
        ListBuffer<JCStatement> savedCurrentStatements = this.currentStatements;
        Symbol savedAllocSym = this.allocSym;
        Symbol savedIsAllocSym = this.isAllocSym;
        JCIdent savedThisId = this.currentThisId;
        JCExpression savedThisExpr = this.currentThisExpr;
        IArithmeticMode savedMode = this.currentArithmeticMode;
        
        if (that.sym.isInterface()) {
            result = that; classBiMap.put(that,that); return;
        }
        try {
            this.classDecl = that;
            this.methodDecl = null;
            this.currentArithmeticMode = Arithmetic.Math.instance(context).defaultArithmeticMode(classDecl.sym,false);
            
            if(jmltest) {
                this.currentThisId = makeThisId(classDecl.pos, classDecl.sym);
                this.currentThisExpr = currentThisId;
            }
            
            this.classDefs = new ListBuffer<JCTree>();
            this.currentStatements = null;

            if (jmltest) {
                JCVariableDecl d = treeutils.makeStaticVarDef(syms.intType,heapVarName,classDecl.sym,
                    treeutils.makeIntLiteral(0, 0));
                heapSym = d.sym;
                //initialStatements.add(d);
                this.classDefs.add(d);
            }
            
            {
                JCVariableDecl d = treeutils.makeVarDef(syms.intType,names.fromString(Strings.allocName),classDecl.sym,
                        treeutils.makeNullLiteral(classDecl.pos));
                allocSym = d.sym;
                d = treeutils.makeVarDef(syms.booleanType,names.fromString(Strings.isAllocName),classDecl.sym,
                        treeutils.makeNullLiteral(classDecl.pos));
                isAllocSym = d.sym;
            }
            
            enclosingClass = that.sym;
            
            int count = 0;
            
            for (JCTree t: that.defs) {
                JmlTestDS obj = new JmlTestDS();
                count++;
                scan(t, jmltest, obj, count);
            }
            
            // FIXME - need to fixup RAC and ESC check o fstatic initialization
            if (!pureCopy) {
                JCBlock bl = checkStaticInitialization();
                if (bl != null) this.classDefs.add(bl);
            }
            
            JmlSpecs.TypeSpecs tyspecs = that.typeSpecs;
            if (!rac) if (tyspecs != null) {
                for (JmlTypeClause t: tyspecs.clauses) {
                    switch (t.token){
                        case REPRESENTS:
                            boolean pv = checkAccessEnabled;
                            checkAccessEnabled = false; // Do not check access in JML clauses
                            try {
                                scan(t);
                            } finally {
                                checkAccessEnabled = pv;
                            }
                            break;
                        case INVARIANT:
                        case CONSTRAINT:
                        case INITIALLY:
                        case AXIOM:
                        case IN:
                        case MAPS:
                        case READABLE:
                        case WRITABLE:
                            // skip
                            break;
                        default:
                            log.error(t.pos,"jml.internal","Clause type not handled in visitJmlClassDecl: " + t.token.internedName());
                    }
                }
            List<JCTree> defs = this.classDefs.toList();
            
            for (JCTree def: defs) {
                if (def instanceof JmlMethodDecl) {
                    JmlMethodDecl jdef = (JmlMethodDecl)def;
                    String nm = jdef.name.toString();
                    if (attr.isModel(jdef.sym) && nm.startsWith(Strings.modelFieldMethodPrefix)) {
                        if ((jdef.mods.flags & Utils.JMLADDED) != 0) {
                            // We are presuming that all represents clauses are processed
                            // (as part of scanning the specs defs in visitJmlClassDecl)
                            // before we handle all the model field methods.
                            utils.warning(jdef.source(),jdef.pos,"jml.no.model.method.implementation",nm.substring(Strings.modelFieldMethodPrefix.length())); // FIXME - extract name of model field
                        }
                    }
                }
            }
            
            // FIXME - replicate all the other AST nodes
            List<JCTypeParameter> typarams = that.typarams;
            if (fullTranslation) typarams = convert(typarams);
            JmlClassDecl n = M.at(that).ClassDef(convert(that.mods),that.name,typarams,convertExpr(that.extending),convertExprList(that.implementing),defs);
            n.sym = that.sym;
            n.setType(that.type);
            n.superSymbol = that.superSymbol;
            n.thisSymbol = that.thisSymbol;
            n.toplevel = that.toplevel;  // FIXME - translate to new top level
            n.docComment = that.docComment;
            n.env = that.env; // FIXME - translate?
            n.specsDecl = that.specsDecl; // FIXME - these may be self-references - and I think there are now only one
            n.typeSpecs = null; //that.typeSpecs; // not copied - FIXME? here and elsewhere
            if (savedClassDefs != null && n.sym.owner instanceof ClassSymbol) {
                savedClassDefs.add(n);
            } else if (currentStatements != null) {
                addStat(n);
            }
            result = n;
            classBiMap.put(that,n);
            } 
        }
           finally {
                this.classDecl = savedClassDecl;
                this.methodDecl = savedMethodDecl;
                this.classDefs = savedClassDefs;
                this.currentThisId = savedThisId;
                this.currentThisExpr = savedThisExpr;
                this.currentStatements = savedCurrentStatements;
                this.allocSym = savedAllocSym;
                this.isAllocSym = savedIsAllocSym;
                this.currentArithmeticMode = savedMode;
                Main.instance(context).popOptions();
        }
            
        
    }
    
    /** Returns a translation of a list of expression, possibly pushing additional
     * statements onto 'currentStatements'
     */
    public @Nullable List<JCExpression> convertExprList(@Nullable List<? extends JCExpression> trees) {
        if (trees==null) return null;
        ListBuffer<JCExpression> newlist = new ListBuffer<JCExpression>();
        for (JCExpression t: trees) {
            scan(t);
            if (eresult == null) eresult = t;
            newlist.add(eresult);
            if (localVariables.isEmpty()) exprBiMap.put(t,eresult);
        }
        return newlist.toList();
    }
    
    /** Returns a translation of an expression, possibly pushing additional
     * statements onto 'currentStatements'
     */
    public @Nullable JCExpression convertExpr(@Nullable JCExpression tree) {
        eresult = null; // Just so it is initialized in case assignment is forgotten
        if (tree != null) {
            super.scan(tree);
            if (rac && eresult != null && eresult.type != null && jmltypes.isJmlType(eresult.type)) eresult.type = jmltypes.repSym((JmlType)eresult.type).type;
            if (localVariables.isEmpty()) exprBiMap.put(tree,eresult);
        }
        return eresult;
    }
    
    /** (Public API) Converts a non-expression AST, returning the converted tree;
     * this may be called externally on ClassDecl and CompilationUnit
     * trees, but should not be called outside of JmlAssertionAdder
     * on trees lower in the AST. In purecopy mode, T can be any JCTree derived
     * type;  but otherwise, it may only be either JCTree or JCExpression
     * (possibly JCStatement) */
    @SuppressWarnings("unchecked")
    public @Nullable <T extends JCTree> T convert(@Nullable T tree) {
        if (tree == null) { result = null; return null; }
        scan(tree);

        if (localVariables.isEmpty()) exprBiMap.put(tree, result);

        return (T)result;
    }
    
    /** Returns a translation of a list of tree, possibly pushing additional
     * statements onto 'currentStatements'; the same restrictions on T apply
     * as above.
     */
    public @Nullable <T extends JCTree> List<T> convert(@Nullable List<T> trees) {
        if (trees==null) return null;
        ListBuffer<T> newlist = new ListBuffer<T>();
        for (T t: trees) {
            newlist.add(convert(t));
        }
        return newlist.toList();
    }
    
    /** Returns a translation of a list of tree, possibly pushing additional
     * statements onto 'currentStatements'; the same restrictions on T apply
     * as above.
     */
    public @Nullable <T extends JCTree> java.util.List<T> convert(@Nullable java.util.List<T> trees) {
        if (trees==null) return null;
        java.util.List<T> newlist = new LinkedList<T>();
        for (T t: trees) {
            newlist.add(convert(t));
        }
        return newlist;
    }
    
    /** (Public API) Reinitializes the object to start a new class or compilation unit or method */
    public void initialize() {
        this.showRacSource = JmlOption.isOption(context,JmlOption.RAC_SHOW_SOURCE);
        this.racCheckAssumeStatements = JmlOption.isOption(context,JmlOption.RAC_CHECK_ASSUMPTIONS);
        this.javaChecks = esc || (rac && JmlOption.isOption(context,JmlOption.RAC_JAVA_CHECKS));
        this.count = 0;
        this.assertCount = 0;
        this.precount = 0;
        this.preparams.clear();
        this.preconditions.clear();
        //this.labels.clear();
        this.pureCopy = !(esc||rac);
        this.treeMap.clear();
        this.oldenv = null;
        this.heapCount = 0;
        this.oldHeapValues.put(names.fromString(""), this.heapCount);
        this.heapVarName = names.fromString("_heap__"); // FIXME - cf. BasicBlocker2
        this.applyNesting = 0;
     //   racMessages.clear();
    //    escMessages.clear();
        assumptionChecks.clear();
        assumptionCheckStats.clear();
        this.useMethodAxioms = !JmlOption.isOption(context,JmlOption.MINIMIZE_QUANTIFICATIONS);
    }
    
    public void visitJmlMethodDecl(JmlMethodDecl that, boolean jmltest) {
        
        String nm = that.name.toString();
        
        if (classDecl == null) classDecl = utils.getOwner(that);
        log.useSource(that.source());
        
        try {
            
            JmlTestDS jmltestdsObj = new JmlTestDS();
            
           // jmltestdsObj.setBody(that.body.stats.get(0));
            jmltestdsObj.setMethodName(that.name.toString());
            jmltestdsObj.setMethodSpecs(that.methodSpecsCombined);
            jmltestdsObj.setModifier(that.mods);
            jmltestdsObj.setParams(that.params);
            jmltestdsObj.setReturnType(that.restype);
            
            JCBlock body = null;
            JCModifiers modifier = null;
            JCExpression rettype;
            List<JCVariableDecl> parameters = null;
            MethodSpecs methodSpecs;
                   
            body = that.body;
            modifier = that.mods;
            rettype = that.restype;
            parameters = that.params;
            
         //   List <JCExpression?JMlMethodDecl> def = ArrayList<JCExpression>();
            
            
            
            {
                this.methodDecl = that;
                this.classDecl = classDecl != null ? classDecl : utils.getOwner(methodDecl) ;
                
                boolean callingSuper = false;
                boolean callingThis = false;
                Iterator<JCStatement> iter = null;
                if (methodDecl.body != null) {
                    iter = methodDecl.body.stats.iterator();
                    if (iter.hasNext()) {
                        JCStatement st = methodDecl.body.stats.get(0);
                    }
                }
            }
            
            
            
        } catch (JmlNotImplementedException e) {
            // FIXME _ if it is actually the synthetic method for a model field we used to use this
            //notImplemented("represents clause containing ", ee, that.source());
            if (that.name.toString().startsWith(Strings.modelFieldMethodPrefix)) {
                notImplemented("represents clause containing ",e);
            } else {
                notImplemented("method (or represents clause) containing ",e);
            }
            log.error(e.pos,"jml.unrecoverable", "Unimplemented construct in a method or model method or represents clause");
        } 

    }
    
 // FIXME - this is a hack - fix and document
    // These are used so that we don't send repeated notImplemented messages
    static Set<String> racMessages = new HashSet<String>();
    static Set<String> escMessages = new HashSet<String>();
    
    /** Issues a diagnostic message (note) containing the message in the given
     * exception.
     */
    protected void notImplemented(String location, JmlNotImplementedException source) {
        String message = location + source.getMessage();
        String key = source.pos.getPreferredPosition() + message;
        if (rac ? !racMessages.add(key) : !escMessages.add(key)) return;
        log.note(source.pos, 
                rac ? "rac.not.implemented" : "esc.not.implemented", 
                message);
    }

}
