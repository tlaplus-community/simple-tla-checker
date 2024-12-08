package us.tlapl;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SymbolNode;
import util.UniqueString;

/**
 * A state, which is an assignment of values to variables.
 */
class State {
	
	/**
	 * A partially-constructed state; some variables have undefined values or
	 * values that could change.
	 */
	static class Partial {
		
		private final Map<Integer, UniqueString> variableNames = new HashMap<Integer, UniqueString>();

		private final Map<Integer, Object> values = new HashMap<Integer, Object>();
		
		Partial(OpDeclNode... variables) {
			for (OpDeclNode variable : variables) {
				this.variableNames.put(variable.getUid(), variable.getName());
				this.values.put(variable.getUid(), null);
			}
		}
		
		void assignValue(SymbolNode variable, Object value) {
			this.values.put(variable.getUid(), value);
		}
		
		State complete() throws IllegalArgumentException {
			List<String> unassigned =
				this.values
				.entrySet()
				.stream()
				.filter(entry -> null == entry.getValue())
				.map(entry -> this.variableNames.get(entry.getKey()).toString())
				.collect(Collectors.toList());
			if (unassigned.isEmpty()) {
				return new State(this);
			} else {
				throw new IllegalArgumentException(
					"Incomplete state definition; the following variables are not assigned a value: "
					+ String.join(", ", unassigned)
				);
			}
		}
	}
	
	private final Map<Integer, Object> values;
	
	private State(Partial state) {
		this.values = state.values;
	}
	
	long getStateHash() {
		return 0;
	}
}