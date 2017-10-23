package org.jmlspecs.openjml.jmltest;

import javax.tools.JavaFileObject;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.IJmlTree;
import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.IInJML;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSource;

import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.JCTree.Visitor;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;

public class JmlTestJmlTree implements IJmlTree{
    
    static boolean isJML(long flags) {
        return (flags & Utils.JMLBIT) != 0;
    }
    
    public static class JmlClassDecl extends JCTree.JCClassDecl implements JmlSource, IInJML {
        
        /** This is the class declaration that holds the specifications for the
         * containing class. It may be the same as the containing class, or a different AST
         * (e.g., from a .jml file), or null if there are no specifications for this class.
         * A class declaration in a .jml file will have a null value for this field.
         */
        public /*@Nullable*/ JmlClassDecl specsDecl;

        /** This field holds the class-level specifications for the type corresponding
         * to this declaration; it is an alias for the specs that are found in the JmlSpecs database
         */
        public JmlSpecs.TypeSpecs typeSpecs;

        /** The top-level tree that this class declaration belongs to; for specification
         * declarations this is the compilation unit containing the spec declaration, which
         * may be different than the compilation unit containing the java class declaration. 
         * Note that the sourcefile for this class declaration can be obtained from
         * toplevel.sourcefile*/
        public JmlCompilationUnit toplevel;
        
        // FIXME - is this used; why would it not be in JCClassDecl?
        public String docComment = null;
        
        /** The scope environment for this class declaration.
         * For a source file, this is the same as typeEnvs.get()
         * but for a specifications file it may be different.
         */
        public Env<AttrContext> env;
        
        /** Set during attribution, used during RAC - the value in Enter is 
         * removed by then.
         */
        public VarSymbol thisSymbol;
        public VarSymbol superSymbol;
        
        public JCBlock initializerBlock;
        public Env<AttrContext> initializerBlockEnv;
        public JCBlock staticInitializerBlock;
        public Env<AttrContext> staticInitializerBlockEnv;
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        protected JmlClassDecl(JCModifiers mods, Name name,
                List<JCTypeParameter> typarams, JCExpression extending,
                List<JCExpression> implementing, List<JCTree> defs,
                ClassSymbol sym) {
            super(mods, name, typarams, extending, implementing, defs, sym);
            specsDecl = null;
            typeSpecs = null;
        }
        
        /** The source this class was declared int - may be different than the top-level compilation
         * unit after model classes are moved around, etc.
         */
        public JavaFileObject sourcefile;
        
        /** The source this class was declared in (model classes may be declared
         * in a source file different than the class that owns the model class)
         */
        @Override
        public JavaFileObject source() { return sourcefile; }


        @Override
        public void accept(Visitor v, boolean jmltest) {
            if(v instanceof IJmlVisitor) {
                ((IJmlVisitor) v).visitJmlClassDecl(this, jmltest);
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v, jmltest);
            }
        }


        @Override
        public boolean isJML() {
            return JmlTestJmlTree.isJML(mods.flags);
        }
        
        
        
    }
    
    public static class JmlMethodDecl extends JCTree.JCMethodDecl implements JmlSource, IInJML {
        
        /** The file containing this declaration */
        public JavaFileObject sourcefile;

        /** The declaration in the jml file, 
         * or null if there is a jml file but no declaration of this method in it, 
         * or the same as the java declaration if there is no jml file
         * (set in JmlMemberEnter); set to self in the parser for 
         * methods in anonymous classes.
         */
        @Nullable public JmlMethodDecl specsDecl; 
        
        /** The constructor for the AST node - but use the factory to get new nodes, not this */
        public JmlMethodDecl(JCModifiers mods, Name name, JCExpression restype,  // FIXME - backdoor use - should not be public
                List<JCTypeParameter> typarams, JCVariableDecl recvparam, List<JCVariableDecl> params,
                List<JCExpression> thrown, JCBlock body,
                JCExpression defaultValue, MethodSymbol sym) {
            super(mods, name, restype, typarams, recvparam, params, thrown, body, defaultValue, sym);
            specsDecl = null;
            sourcefile = null;
        }
        
        @Override
        public void accept(Visitor v, boolean jmltest) {
            if (v instanceof IJmlVisitor) {
                ((IJmlVisitor)v).visitJmlMethodDecl(this, jmltest); 
            } else {
                // unexpectedVisitor(this,v);
                super.accept(v);
            }
        }

        @Override
        public boolean isJML() {
            return JmlTestJmlTree.isJML(mods.flags);
        }

        @Override
        public JavaFileObject source() {
            return sourcefile;
        }
    }
    
    
    
    
    
    

}
