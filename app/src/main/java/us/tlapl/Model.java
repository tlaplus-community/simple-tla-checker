package us.tlapl;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.SyntaxTreeConstants;

/**
 * Functions for generating next & initial states of a model, checking
 * invariants, etc.
 */
class Model {
	
	/**
	 * The spec's semantic parse tree.
	 */
	private final ModuleNode root;
	
	/**
	 * The next-state relation.
	 */
	private final OpApplNode next;
	
	/**
	 * Construct a new {@link Model} instance. Finds and validates the next-
	 * state relation.
	 * @param root The spec's semantic parse tree.
	 */
	Model(ModuleNode root) {
		this.root = root;
		OpDefNode next = this.findDefinition("Next");
		ExprNode nextExpr = next.getBody();
		if (next.getArity() != 0) {
			throw new IllegalArgumentException("Next definition must not take any parameters");
		}
		if (next.level != LevelConstants.ActionLevel) {
			throw new IllegalArgumentException("Next definition must be action level, not " + SemanticNode.levelToString(next.level));
		}
		if (!(nextExpr instanceof OpApplNode)) {
			throw new IllegalArgumentException("Next body must be operator application node");
		}
		OpApplNode body = (OpApplNode)nextExpr;
		if (body.getOperator().getName() != ASTConstants.OP_dl) {
			throw new IllegalArgumentException("Next must be list of disjuncts, not " + SyntaxTreeConstants.SyntaxNodeImage[nextExpr.getTreeNode().getKind()]);
		}
		this.next = body;
	}
	
	private OpDefNode findDefinition(String name) throws IllegalArgumentException {
		return Arrays.stream(this.root.getOpDefs())
			.filter((op) -> op.getName().toString().equals(name))
			.findFirst()
			.orElseThrow(() -> new IllegalArgumentException("Spec must contain definition " + name));
	}
	
	/**
	 * Get all of the model's initial states. Currently, this just searches
	 * for a definition named "Init" and assumes it is of the form:
	 *
	 * Init ==
	 *   /\ v1 = constExpr1
	 *   /\ v2 = constExpr2
	 *   ...
	 *
	 * So it's restricted to a conjunction list, with each conjunct defining
	 * a single variable with a constant expression (not referring to other
	 * variables, for example). This is a highly restricted form compared to
	 * what is theoretically possible, but suffices for prototyping.
	 * @return A list of the model's initial states.
	 */
	List<State> getInitialStates() {
		OpDefNode init = this.findDefinition("Init");
		ExprNode initExpr = init.getBody();
		
		// Various restrictions on the form Init can take.
		if (init.getArity() != 0) {
			throw new IllegalArgumentException("Init definition must not take any parameters");
		}
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
		
		// Use Init to derive initial value of each spec variable.
		State.Partial initialState = new State.Partial(this.root.getVariableDecls());
		for (ExprOrOpArgNode conjunct : body.getArgs()) {
			if (!(conjunct instanceof OpApplNode)) {
				throw new IllegalArgumentException("Conjunct must be operator application node");
			}
			OpApplNode equals = (OpApplNode)conjunct;
			if (!equals.getOperator().getName().toString().equals("=")) {
				throw new IllegalArgumentException("Conjunct must be single '=' statement");
			}
			SymbolNode variable = ((OpApplNode)equals.getArgs()[0]).getOperator();
			ExprNode value = (ExprNode)equals.getArgs()[1];
			initialState.assignValue(variable, Expression.eval(value));
		}
		ArrayList<State> initialStates = new ArrayList<State>();
		initialStates.add(initialState.complete());
		return initialStates;
	}
	
	/**
	 * Given the current state, generate all next states under the model.
	 * Currently this works by searching for a definition named "Next", and
	 * assuming it is of the following form:
	 *
	 * Next ==
	 *   \/ Action1
	 *   \/ Action2
	 *   ...
	 *
	 * Where each action is of the following form:
	 *
	 * Action ==
	 *   /\ v1 = expr1
	 *   /\ v2 = expr2
	 *   ...
	 *
	 * Thus each action generates a single state. This suffices for
	 * prototyping.
	 * @param current
	 * @return
	 */
	List<State> getSuccessorStates(State current) {
		return Arrays.stream(this.next.getArgs())
			.map(disjunct -> resolveAction(disjunct))
			.map(action -> getStateFromAction(current, action))
			.collect(Collectors.toList());
	}
	
	ExprNode resolveAction(ExprOrOpArgNode disjunct) {
		throw new UnsupportedOperationException("Resolving action");
	}
	
	State getStateFromAction(State current, ExprNode action) {
		throw new UnsupportedOperationException("Getting next state from action");
	}
	
	boolean satisfiesInvariants(State current) {
		return true;
	}
}