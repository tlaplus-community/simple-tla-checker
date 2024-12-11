package us.tlapl;

import tla2sany.parser.ParseException;
import tla2sany.semantic.AbortException;

public class Errors {
	
	/**
	 * CLI exit codes.
	 */
	public static final int SUCCESS = 0;
	public static final int INVALID_CLI_PARAMS = 1;
	public static final int MODULE_RESOLUTION_FAILURE = 2;
	public static final int SYNTAX_PARSING_FAILURE = 10;
	public static final int SEMANTIC_CHECKING_FAILURE = 11;
	public static final int LEVEL_CHECKING_FAILURE = 12;
	public static final int INVARIANT_FAILURE = 20;
	
	public static abstract class CheckerError extends Exception {
		private static final long serialVersionUID = 1L;
		public CheckerError(String message) {
			super(message);
		}
		public abstract int getErrorCode();
	}
	
	public static class ModuleResolutionFailure extends CheckerError {
		private static final long serialVersionUID = 1L;
		public ModuleResolutionFailure(String moduleName) {
			super("ERROR: Could not find module " + moduleName);
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