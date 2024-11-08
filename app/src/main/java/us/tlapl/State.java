package us.tlapl;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import tla2sany.parser.TLAplusParserConstants;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
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
		
		// Check to ensure definition is of proper form
		/*
		if (init.getArity() != 0) {
			throw new IllegalArgumentException("Init definition must not take any parameters");
		}
		*/
		if (initExpr.level != LevelConstants.ConstantLevel && initExpr.level != LevelConstants.VariableLevel) {
			throw new IllegalArgumentException("Init definition must be of constant or variable level, not " + SemanticNode.levelToString(initExpr.level));
		}
		if (!(initExpr instanceof OpApplNode)) {
			throw new IllegalArgumentException("Init body must be operator application node");
		}
		OpApplNode body = (OpApplNode)initExpr;
		if (body.getOperator().getName() != ASTConstants.OP_cl) {
			throw new IllegalArgumentException("Init must be list of conjuncts, not " + SyntaxTreeConstants.SyntaxNodeImage[initExpr.getTreeNode().getKind()]);
		}
		
		// Evaluate Init definition; support list of conjuncts, each setting
		// the value of a specific variable using a constant-level equals
		// expression.
		State initialState = new State();
		for (OpDeclNode variable : root.getVariableDecls()) {
			initialState.values.put(variable.getUid(), null);
		}
		for (ExprOrOpArgNode conjunct : body.getArgs()) {
			if (!(initExpr instanceof OpApplNode)) {
				throw new IllegalArgumentException("Conjunct must be operator application node");
			}
			OpApplNode equals = (OpApplNode)conjunct;
			if (!equals.getOperator().getName().toString().equals("=")) {
				throw new IllegalArgumentException("Conjunct must be single = statement");
			}
			SymbolNode variable = ((OpApplNode)equals.getArgs()[0]).getOperator();
			ExprNode value = (ExprNode)equals.getArgs()[1];
			initialState.values.put(variable.getUid(), Expression.valueOf(value));
		}
		for (int uid : initialState.values.keySet()) {
			if (null == initialState.values.get(uid)) {
				throw new IllegalArgumentException("Failed to assign value to variable in initial state");
			}
		}
		ArrayList<State> initialStates = new ArrayList<State>();
		initialStates.add(initialState);
		return initialStates;
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