package us.tlapl;

import tla2sany.semantic.AtNode;
import tla2sany.semantic.DecimalNode;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.ExprNode;

public class Expression {
	static Object eval(ExprNode expr) {
		if (expr instanceof AtNode) {
			throw new UnsupportedOperationException("At node type not supported");
		} else if (expr instanceof DecimalNode) {
			throw new UnsupportedOperationException("Non-integers are not supported");
		} else if (expr instanceof LabelNode) {
			throw new UnsupportedOperationException("Labels are not supported");
		} else if (expr instanceof LetInNode) {
			throw new UnsupportedOperationException("LET-IN not supported");
		} else if (expr instanceof NumeralNode) {
			NumeralNode value = (NumeralNode)expr;
			return value.val();
		} else if (expr instanceof OpApplNode) {
			OpApplNode opAppl = (OpApplNode)expr;
			throw new UnsupportedOperationException("Operator application not supported");
		} else if (expr instanceof StringNode) {
			StringNode value = (StringNode)expr;
			return value.getRep();
		} else if (expr instanceof SubstInNode) {
			throw new UnsupportedOperationException("SubstIn not supported");
		} else {
			throw new UnsupportedOperationException("Unrecognized expression type");
		}
	}
	
}