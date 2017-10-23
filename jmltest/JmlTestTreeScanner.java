package org.jmlspecs.openjml.jmltest;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.Visitor;

public class JmlTestTreeScanner extends Visitor{
    
    public void scan(JCTree tree, boolean jmltest, JmlTestDS jmltestobj, int count) {
        if(tree!=null)  tree.accept(this);
    }
    
    public void scan(JCTree tree, boolean jmltest) {
        if(tree!=null) tree.accept(this, jmltest);
    } 
    
    public void scan(JCTree tree) {
        if(tree!=null) tree.accept(this);
    }

}
