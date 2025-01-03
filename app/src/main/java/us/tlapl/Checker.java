package us.tlapl;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import tla2sany.parser.ParseException;

/**
 * Top-level BFS loop for model-checking a TLA⁺ file.
 */
public class Checker {
	
	/**
	 * Main entrypoint to the program. Takes a single CLI parameter: the path
	 * to the spec.
	 * @param args The CLI parameters.
	 * @throws IOException 
	 */
	public static void main(String... args) throws ParseException {
		if (args.length > 0) {
			Path specPath = Path.of(args[0]);
			int result = run(specPath);
			System.exit(result);
		} else {
			System.err.println("Missing CLI parameter: spec path");
			System.exit(Errors.INVALID_CLI_PARAMS);
		}
	}

	/**
	 * Reads & parses spec then checks model.
	 * @param spec Path to spec file.
	 * @return Error code; {@link SUCCESS} on success.
	 */
	static int run(Path spec) throws ParseException {
		try {
			Parser.Result parsed = Parser.parse(spec);
			Model model = new Model(parsed);
			List<State> failureTrace = check(model);
			if (null == failureTrace) {
				System.out.println("Success!");
				return Errors.SUCCESS;
			} else {
				System.err.println("Failure.");
				System.err.println(failureTrace.toString());
				return Errors.INVARIANT_FAILURE;
			}
		} catch (Errors.CheckerError e) {
			System.err.println(e.toString());
			return e.getErrorCode();
		}
	}
	
	/**
	 * Runs a breadth-first search on the given spec, until either all states
	 * are exhausted or an invariant failure is found.
	 * @param model The spec model to check.
	 * @return A trace to a state violating an invariant; null if successful.
	 */
	static List<State> check(Model model) {
		Map<Long, Long> predecessors = new HashMap<Long, Long>();
		Deque<State> queue = new ArrayDeque<State>();
		List<State> initialStates = model.getInitialStates();
		queue.addAll(initialStates);
		for (State init : initialStates) {
			predecessors.put(init.getStateHash(), 0L);
		}

		while (!queue.isEmpty()) {
			State current = queue.removeFirst();
			long currentHash = current.getStateHash();
			for (State next : model.getSuccessorStates(current)) {
				long nextHash = next.getStateHash();
				if (!predecessors.containsKey(nextHash)) {
					predecessors.put(nextHash, currentHash);
					if (!model.satisfiesInvariants(next)) {
						return reconstructStateTrace(model, predecessors, next);
					}
					queue.push(next);
				}
			}
		}
		
		return null;
	}
	
	/**
	 * Given a predecessor graph and a target node, constructs a trace from
	 * the initial state to the target state. This is done by using the
	 * predecessor graph to build a list of state hashes from the target
	 * state back to the initial state, then reversing that list and
	 * constructing a trace by starting at the initial state, checking all
	 * next states, finding which one matches the expected state hash, then
	 * repeating that process for the matching state until the target state
	 * is reached.
	 * @param Model The spec model.
	 * @param predecessors Map each state's hash to its predecessor.
	 * @param last The target state to construct a trace to.
	 * @return A sequence of states from initial state to target.
	 */
	static List<State> reconstructStateTrace(Model model, Map<Long, Long> predecessors, State last) {
		LinkedList<Long> hashes = new LinkedList<Long>();
		long current = last.getStateHash();
		while (current != 0L) {
			hashes.addFirst(current);
			current = predecessors.get(current);
		}
		
		ArrayList<State> trace = new ArrayList<State>();
		List<State> nextStates = model.getInitialStates();
		for (long nextStateHash : hashes) {
			State nextState = null;
			for (State candidate : nextStates) {
				if (nextStateHash == candidate.getStateHash()) {
					nextState = candidate;
					break;
				}
			}
			if (null == nextState) {
				throw new RuntimeException("ERROR: Unable to reconstruct state trace.");
			} else {
				trace.add(nextState);
				nextStates = model.getSuccessorStates(nextState);
			}
		}
		return trace;
	}
}