package us.tlapl;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import tla2sany.semantic.ModuleNode;

public class Checker {
	
	static List<State> reconstructStateTrace(ModuleNode root, Map<Long, Long> predecessors, State last) {
		LinkedList<Long> hashes = new LinkedList<Long>();
		long current = last.getStateHash();
		while (current != 0L) {
			hashes.addFirst(current);
			current = predecessors.get(current);
		}
		
		ArrayList<State> trace = new ArrayList<State>();
		List<State> nextStates = State.getInitialStates(root);
		for (long nextStateHash : hashes) {
			State nextState = null;
			for (State candidate : nextStates) {
				if (nextStateHash == candidate.getStateHash()) {
					nextState = candidate;
					break;
				}
			}
			if (null == nextState) {
				System.err.println("ERROR: Unable to reconstruct state trace.");
			} else {
				trace.add(nextState);
				nextStates = nextState.getSuccessorStates(root);
			}
		}
		return trace;
	}
	
	static List<State> check(ModuleNode root) {
		Map<Long, Long> predecessors = new HashMap<Long, Long>();
		Deque<State> queue = new ArrayDeque<State>();
		List<State> initialStates = State.getInitialStates(root);
		queue.addAll(initialStates);
		for (State init : initialStates) {
			predecessors.put(init.getStateHash(), 0L);
		}

		while (!queue.isEmpty()) {
			State current = queue.removeFirst();
			long currentHash = current.getStateHash();
			for (State next : current.getSuccessorStates(root)) {
				long nextHash = next.getStateHash();
				if (!predecessors.containsKey(nextHash)) {
					predecessors.put(nextHash, currentHash);
					if (!next.satisfiesInvariants(root)) {
						return reconstructStateTrace(root, predecessors, next);
					}
					queue.push(next);
				}
			}
		}
		
		return null;
	}
	
    public static void main(String[] args) throws IOException {
    	if (args.length > 0) {
   			Path spec = Path.of(args[0]);
    		try {
    			ModuleNode root = Parser.parse(spec);
    			List<State> failureTrace = check(root);
    			if (null == failureTrace) {
    				System.out.println("Success!");
    			} else {
    				System.out.println("Failure.");
    				System.out.println(failureTrace.toString());
    			}
    		} catch (IOException e) {
              System.err.println("Failed to read file " + spec.toString());
            }
    	} else {
    		System.err.println("Missing CLI parameter: spec path");
    	}
    }
}
