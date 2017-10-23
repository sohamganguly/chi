package org.jmlspecs.openjml.jmltest;

import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;

import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.List;

public class JmlTestDS {
    
    public JCBlock body;
    public String methodName;
    public JCModifiers modifier;
    public JCExpression returnType;
    public List<JCVariableDecl> params;
    public MethodSpecs methodSpecs;
    
    
    public JCBlock getBody() {
        return body;
    }
    public void setBody(JCBlock body) {
        this.body = body;
    }
    public String getMethodName() {
        return methodName;
    }
    public void setMethodName(String methodName) {
        this.methodName = methodName;
    }
    public JCModifiers getModifier() {
        return modifier;
    }
    public void setModifier(JCModifiers modifier) {
        this.modifier = modifier;
    }
    public JCExpression getReturnType() {
        return returnType;
    }
    public void setReturnType(JCExpression returnType) {
        this.returnType = returnType;
    }
    
    public MethodSpecs getMethodSpecs() {
        return methodSpecs;
    }
    public void setMethodSpecs(MethodSpecs methodSpecs) {
        this.methodSpecs = methodSpecs;
    }
    public List<JCVariableDecl> getParams() {
        return params;
    }
    public void setParams(List<JCVariableDecl> params) {
        this.params = params;
    }
    
    
    

}
