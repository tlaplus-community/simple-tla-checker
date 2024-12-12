package us.tlapl;

import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Deque;
import java.util.stream.Collectors;

import tla2sany.parser.ParseException;
import tla2sany.semantic.AbortException;

public class Errors {
	
	/**
	 * CLI exit codes.
	 */
	public static final int SUCCESS = 0;
	public static final int INVALID_CLI_PARAMS = 1;
	public static final int MODULE_RESOLUTION_FAILURE = 2;
	public static final int CIRCULAR_MODULE_DEPENDENCY_FAILURE = 3;
	public static final int SYNTAX_PARSING_FAILURE = 10;
	public static final int SEMANTIC_CHECKING_FAILURE = 11;
	public static final int LEVEL_CHECKING_FAILURE = 12;
	public static final int INVARIANT_FAILURE = 20;
	
	public static abstract class CheckerError extends Exception {
		private static final long serialVersionUID = 1L;
		public CheckerError(String message) {
			super(message);
		}
		public CheckerError() { }
		public abstract int getErrorCode();
	}
	
	public static class ModuleResolutionFailure extends CheckerError {
		private static final long serialVersionUID = 1L;
		public ModuleResolutionFailure(String moduleName, Path... moduleSearchPaths) {
			super(
				"ERROR: Could not find module " + moduleName + " in search paths:\n"
				+ Arrays.stream(moduleSearchPaths).map(path -> path.toString()).collect(Collectors.joining("\n"))
			);
		}
		public ModuleResolutionFailure(InvalidPathException e) {
			super(e.toString());
		}
		public int getErrorCode() {
			return MODULE_RESOLUTION_FAILURE;
		}
	}
	
	public static class CircularModuleDependencyFailure extends CheckerError {
		private static final long serialVersionUID = 1L;
		private final Deque<String> dependencyChain;
		private final String firstOpened;
		private final String dependsOnFirstOpened;
		public CircularModuleDependencyFailure(Deque<String> dependencyChain, String firstOpened, String dependsOnFirstOpened) {
			this.dependencyChain = dependencyChain;
			this.firstOpened = firstOpened;
			this.dependsOnFirstOpened = dependsOnFirstOpened;
		}
		public String getMessage() {
			StringBuilder sb = new StringBuilder();
			sb.append("ERROR: Circular module dependency:\n");
			if (this.firstOpened.equals(this.dependsOnFirstOpened)) {
				sb.append("Module " + this.firstOpened + " imports itself.");
				return sb.toString();
			}
			sb.append(String.format(
				"Module %1$s depends on %2$s, but %2$s imports %1$s as follows:\n",
				this.dependsOnFirstOpened,
				this.firstOpened
			));
			String current = this.dependencyChain.pop();
			for (String next : this.dependencyChain) {
				sb.append(String.format("  %s imports %s\n", next, current));
				current = next;
				if (next == this.firstOpened) {
					break;
				}
			}
			return sb.toString();
		}
		public int getErrorCode() {
			return MODULE_RESOLUTION_FAILURE;
		}
	}
	
	public static class SyntaxParsingFailure extends CheckerError {
		private static final long serialVersionUID = 1L;
		public SyntaxParsingFailure(ParseException e) {
			super(e.toString());
		}
		public int getErrorCode() {
			return SYNTAX_PARSING_FAILURE;
		}
	}
	
	public static class SemanticCheckingFailure extends CheckerError {
		private static final long serialVersionUID = 1L;
		public SemanticCheckingFailure(AbortException e) {
			super("ERROR: Semantic checking failed:\n" + e.toString());
		}
		public SemanticCheckingFailure(tla2sany.semantic.Errors log) {
			super("ERROR: Semantic checking failed:\n" + log.toString());
		}
		public int getErrorCode() {
			return SEMANTIC_CHECKING_FAILURE;
		}
	}
	
	public static class LevelCheckingFailure extends CheckerError {
		private static final long serialVersionUID = 1L;
		public LevelCheckingFailure(tla2sany.semantic.Errors log) {
			super("ERROR: Level checking failed:\n" + log.toString());
		}
		public int getErrorCode() {
			return LEVEL_CHECKING_FAILURE;
		}
	}
}