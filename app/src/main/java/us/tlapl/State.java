package us.tlapl;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import tla2sany.semantic.ExprNode;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;

class State {
	
	private final Map<Integer, Object> values = new HashMap<Integer, Object>();
	
	static List<Object> getInitialValuesForVariable(ModuleNode root, OpDeclNode variable) {
		return null;
	}
	
	static List<State> getInitialStates(ModuleNode root) {
		// Get Init definition
		OpDefNode init =
			Arrays.stream(root.getOpDefs())
			.filter((op) -> op.getName().toString().equals("Init"))
			.findFirst()
			.orElseThrow(() -> new IllegalArgumentException("Spec must contain Init definition"));
		ExprNode initExpr = init.getBody();
		TreeNode initExprSyntax = initExpr.getTreeNode();
		
		// Check to ensure definition is of proper form
		if (init.getArity() != 0) {
			throw new IllegalArgumentException("Init definition must not take any parameters");
		}
		if (initExpr.level != LevelConstants.ConstantLevel && initExpr.level != LevelConstants.VariableLevel) {
			throw new IllegalArgumentException("Init definition must be of constant or variable level, not " + SemanticNode.levelToString(initExpr.level));
		}
		if (!initExprSyntax.isKind(SyntaxTreeConstants.N_ConjList)) {
			throw new IllegalArgumentException("Init must be list of conjuncts, not " + SyntaxTreeConstants.SyntaxNodeImage[initExpr.getKind()]);
		}
		
		// Evaluate Init definition
		return null;
	}
	
	List<State> getSuccessorStates(ModuleNode root) {
		return new ArrayList<State>();
	}
	
	long getStateHash() {
		return 0;
	}
	
	boolean satisfiesInvariants(ModuleNode root) {
		return true;
	}
}