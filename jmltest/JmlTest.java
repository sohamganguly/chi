package org.jmlspecs.openjml.jmltest;

import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.IAPI;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.JCDiagnostic;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.PropagatedException;
import com.sun.tools.javac.util.Log.WriterKind;

public class JmlTest extends JmlTreeScanner{
    
    protected static final Context.Key<JmlTest> testKey = 
            new Context.Key<JmlTest>();
    
    boolean verbose;
    
    public static boolean jmltestdebug = false;
    
    public JmlTestAssertionAdder assertionAdder;
    
    //protected @NonNull String proverToUse; Not Needed in JmlTest
    
    @NonNull Context context;
    @NonNull Symtab syms;
    @NonNull Log log;
    @NonNull Utils utils;
    
    public JmlTest(Context context) {
        
        this.context = context;
        this.syms = Symtab.instance(context);
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        
    }

    public static JmlTest instance (Context context) {
        
        JmlTest instance = context.get(testKey);
        if (instance == null) {
            instance = new JmlTest(context);
            context.put(testKey,instance);
        }
        return instance;
        
    }
    
    public void check(JCTree tree) {
        
        this.verbose = jmltestdebug; //Needs to be completed
        
    //    this.assertionAdder = new JmlTestAssertionAdder(context, false, false); //More changes required
        
        try {
            assertionAdder.convert(tree, true);
            tree.accept(this);
        } catch (PropagatedException e) {
            Main.instance(context).canceled = true;
            throw e;
        } catch (Exception e) {
            log.error("jml.internal", "Internal Error - JmlTest");
        }
        
    }
    
    @Override
    public void visitClassDef(JCClassDecl node) {
        Main.instance(context).pushOptions(node.mods);
        if (node.sym.isInterface()) return;  // Nothing to verify in an interface
            // TODO: not so - could check that specs are consistent
        // The super class takes care of visiting all the methods
        utils.progress(1,1,"Proving methods in " + utils.classQualifiedName(node.sym) ); //$NON-NLS-1$
        super.visitClassDef(node);
        utils.progress(1,1,"Completed proving methods in " + utils.classQualifiedName(node.sym) ); //$NON-NLS-1$
        Main.instance(context).popOptions();
    }
    
    /** When we visit a method declaration, we translate and prove the method;
     * we do not walk into the method any further from this call, only through
     * the translation mechanism.  
     */
    @Override
    public void visitMethodDef(@NonNull JCMethodDecl decl) {
        Main.instance(context).pushOptions(decl.mods);
        IProverResult res = null;
        if (decl.body == null) return; // FIXME What could we do with model methods or interfaces, if they have specs - could check that the preconditions are consistent
        if (!(decl instanceof JmlMethodDecl)) {
            JCDiagnostic d = (log.factory().warning(log.currentSource(), decl.pos(), "jml.internal","Internal Error - JmlTest"));
            log.report(d);
            //log.warning(decl.pos(),"jml.internal","Unexpected non-JmlMethodDecl in JmlEsc - not checking " + utils.qualifiedMethodSig(decl.sym)); //$NON-NLS-2$
      //      res = new ProverResult(proverToUse,ProverResult.ERROR,decl.sym).setOtherInfo(d);
            return;
        }
        JmlMethodDecl methodDecl = (JmlMethodDecl)decl;

        if (skip(methodDecl)) {
  ///          markMethodSkipped(methodDecl," (excluded by skipesc)"); //$NON-NLS-1$
            return;
        }
        // Do any nested classes and methods first (which will recursively call
        // this method)
        super.visitMethodDef(methodDecl);

        if (!filter(methodDecl)) {
 //           markMethodSkipped(methodDecl," (excluded by -method)"); //$NON-NLS-1$ 
            return;
        }
        try {
   //         res = doMethod(methodDecl);
        } catch (PropagatedException e) {
            IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
     //       if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult(proverToUse,IProverResult.CANCELLED,methodDecl.sym));
            throw e;
        }
        Main.instance(context).popOptions();
        return;        
    }
    
    public static boolean skip(JmlMethodDecl methodDecl) {
        if (methodDecl.mods != null) {
            for (JCTree.JCAnnotation a : methodDecl.mods.annotations) {
                if (a != null && a.type.toString().equals("org.jmlspecs.annotation.SkipEsc")) { // FIXME - do this without converting to string
                    return true;
                }
            }
        }
        return false;
    }
    
    // FIXME - perhaps shoud not be in JmlEsc
    public static boolean skipRac(JmlMethodDecl methodDecl) {
        if (methodDecl.mods != null) {
            for (JCTree.JCAnnotation a : methodDecl.mods.annotations) {
                if (a != null && a.type.toString().equals("org.jmlspecs.annotation.SkipRac")) { // FIXME - do this without converting to string
                    return true;
                }
            }
        }
        return false;
    }
    
    /*public IProverResult markMethodSkipped(JmlMethodDecl methodDecl, String reason) {
        utils.progress(2,1,"Skipping proof of " + utils.qualifiedMethodSig(methodDecl.sym) + reason); //$NON-NLS-1$ //$NON-NLS-2$
        
        // FIXME - this is all a duplicate from MethodProverSMT
        IProverResult.IFactory factory = new IProverResult.IFactory() {
            @Override
            public IProverResult makeProverResult(MethodSymbol msym, String prover, IProverResult.Kind kind, java.util.Date start) {
                ProverResult pr = new ProverResult(prover,kind,msym);
                pr.methodSymbol = msym;
                if (start != null) {
                    pr.setDuration((pr.timestamp().getTime()-start.getTime())/1000.);
                    pr.setTimestamp(start);
                }
                return pr;
            }
        };
 //       IProverResult res = factory.makeProverResult(methodDecl.sym,proverToUse,IProverResult.SKIPPED,new java.util.Date());
        IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
        if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, res);
        return res;
    }*/
    
    /** Do the actual work of proving the method */
    /*protected IProverResult doMethod(@NonNull JmlMethodDecl methodDecl) {
        boolean printPrograms = this.verbose || JmlOption.isOption(context, JmlOption.SHOW);

        if (skip(methodDecl)) {
            return markMethodSkipped(methodDecl," (because of SkipEsc annotation)");
        }
        utils.progress(1,1,"Starting proof of " + utils.qualifiedMethodSig(methodDecl.sym) + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)); //$NON-NLS-1$ //$NON-NLS-2$
        log.resetRecord();
//        int prevErrors = log.nerrors;

        IAPI.IProofResultListener proofResultListener = context.get(IAPI.IProofResultListener.class);
        if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult(proverToUse,IProverResult.RUNNING,methodDecl.sym));

        // The code in this method decides whether to attempt a proof of this method.
        // If so, it sets some parameters and then calls proveMethod
        
        boolean isConstructor = methodDecl.sym.isConstructor();
        boolean doEsc = ((methodDecl.mods.flags & (Flags.SYNTHETIC|Flags.ABSTRACT|Flags.NATIVE)) == 0);
            // TODO: Could check that abstract or native methods have consistent specs
        
        // Don't do ESC on the constructor of Object
        // FIXME - why?  (we don't have the source anyway, so how would we get here?)
        if (methodDecl.sym.owner == syms.objectType.tsym && isConstructor) doEsc = false;
        if (!doEsc) return null; // FIXME - SKIPPED?

        // print the body of the method to be proved
        if (printPrograms) {
            PrintWriter noticeWriter = log.getWriter(WriterKind.NOTICE);
            noticeWriter.println(Strings.empty);
            noticeWriter.println("--------------------------------------"); //$NON-NLS-1$
            noticeWriter.println(Strings.empty);
            noticeWriter.println("STARTING PROOF OF " + utils.qualifiedMethodSig(methodDecl.sym)); //$NON-NLS-1$
            noticeWriter.println(JmlPretty.write(methodDecl.body));
        }
        
        IProverResult res = null;
        try {
            if (JmlOption.isOption(context, JmlOption.BOOGIE)) {
                res = new MethodProverBoogie(this).prove(methodDecl);
            } else {
                res = new MethodProverSMT(this).prove(methodDecl,proverToUse);
            }
            utils.progress(1,1,"Completed proof of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                    + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
                    + " - "
                    + (  res.isSat() ? "with warnings" 
                       : res.result() == IProverResult.UNSAT ? "no warnings"
                               : res.result().toString())
                    );
//            if (log.nerrors != prevErrors) {
//                res = new ProverResult(proverToUse,IProverResult.ERROR,methodDecl.sym);
//            }

        } catch (Main.JmlCanceledException | PropagatedException e) {
            res = new ProverResult(proverToUse,ProverResult.CANCELLED,methodDecl.sym); // FIXME - I think two ProverResult.CANCELLED are being reported
           // FIXME - the following will through an exception because progress checks whether the operation is cancelled
            utils.progress(1,1,"Proof ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
            + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
            + " - exception"
            );
            throw e;
        } catch (Exception e) {
            JCDiagnostic d = log.factory().error(log.currentSource(), null, "jml.internal","Prover aborted with exception: " + e.getMessage());
            log.report(d);

            res = new ProverResult(proverToUse,ProverResult.ERROR,methodDecl.sym).setOtherInfo(d);
            //log.error("jml.internal","Prover aborted with exception: " + e.getMessage());
            utils.progress(1,1,"Proof ABORTED of " + utils.qualifiedMethodSig(methodDecl.sym)  //$NON-NLS-1$ 
                    + " with prover " + (Utils.testingMode ? "!!!!" : proverToUse)  //$NON-NLS-1$ 
                    + " - exception"
                    );
            // FIXME - add a message? use a factory?
        } finally {
            if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, res);
            if (proofResultListener != null) proofResultListener.reportProofResult(methodDecl.sym, new ProverResult(proverToUse,IProverResult.COMPLETED,methodDecl.sym));
        }
        return res;
    }*/
        
    /** Return true if the method is to be checked, false if it is to be skipped.
     * A warning that the method is being skipped is issued if it is being skipped
     * and the verbosity is high enough.
     * */
    public boolean filter(JCMethodDecl methodDecl) {
        String fullyQualifiedName = utils.qualifiedName(methodDecl.sym);
        String simpleName = methodDecl.name.toString();
        if (methodDecl.sym.isConstructor()) {
            String constructorName = methodDecl.sym.owner.name.toString();
            fullyQualifiedName = fullyQualifiedName.replace("<init>", constructorName);
            simpleName = simpleName.replace("<init>", constructorName);
        }
        String fullyQualifiedSig = utils.qualifiedMethodSig(methodDecl.sym);

        String excludes = JmlOption.value(context,JmlOption.EXCLUDE);
        if (excludes != null) {
            for (String exclude: excludes.split(";")) { //$NON-NLS-1$
                if (fullyQualifiedName.equals(exclude) ||
                        fullyQualifiedSig.equals(exclude) ||
                        simpleName.equals(exclude)) {
                    if (utils.jmlverbose > Utils.PROGRESS)
                        log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it is excluded by " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                    return false;
                }
                try {
                    if (Pattern.matches(exclude,fullyQualifiedName)) {
                        if (utils.jmlverbose > Utils.PROGRESS)
                            log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it is excluded by " + exclude); //$NON-NLS-1$ //$NON-NLS-2$
                        return false;
                    }
                } catch(PatternSyntaxException e) {
                    // The methodToDo can be a regular string and does not
                    // need to be legal Pattern expression
                    // skip
                }
            }
        }

        String methodsToDo = JmlOption.value(context,JmlOption.METHOD);
        if (methodsToDo != null) {
            match: {
                if (fullyQualifiedSig.equals(methodsToDo)) break match; // A hack to allow at least one signature-containing item in the methods list
                for (String methodToDo: methodsToDo.split(";")) { //$NON-NLS-1$ 
                    if (fullyQualifiedName.equals(methodToDo) ||
                            methodToDo.equals(simpleName) ||
                            fullyQualifiedSig.equals(methodToDo)) {
                        break match;
                    }
                    try {
                        if (Pattern.matches(methodToDo,fullyQualifiedName)) break match;
                    } catch(PatternSyntaxException e) {
                        // The methodToDo can be a regular string and does not
                        // need to be legal Pattern expression
                        // skip
                    }
                }
                if (utils.jmlverbose > Utils.PROGRESS) {
                    log.getWriter(WriterKind.NOTICE).println("Skipping " + fullyQualifiedName + " because it does not match " + methodsToDo);  //$NON-NLS-1$//$NON-NLS-2$
                }
                return false;
            }
        }
        
        return true;
    }
    

}
