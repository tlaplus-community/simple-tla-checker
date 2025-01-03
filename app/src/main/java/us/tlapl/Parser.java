package us.tlapl;

import java.io.IOException;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.Deque;

import tla2sany.semantic.ModuleNode;
import tla2sany.st.TreeNode;
import util.UniqueString;

import java.io.FileInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import tla2sany.parser.ParseException;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Context;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.Generator;

/**
 * Get from spec filepath to semantic graph.
 */
public class Parser {
	
	public static class Result {
		public final TreeNode syntaxTree;
		public final ExternalModuleTable dependencies;
		public final Generator semanticChecker;
		public final ModuleNode semanticTree;
		public final tla2sany.semantic.Errors log;
		public Result(
				TreeNode syntaxTree,
				ExternalModuleTable dependencies,
				Generator semanticChecker,
				ModuleNode semanticTree,
				tla2sany.semantic.Errors log
			) {
			this.syntaxTree = syntaxTree;
			this.dependencies = dependencies;
			this.semanticChecker = semanticChecker;
			this.semanticTree = semanticTree;
			this.log = log;
		}
	}
	
	/**
	 * Reads a spec source file, parses it, then runs semantic analysis and
	 * level-checking on it.
	 * @param spec Path to the spec source file.
	 * @return A parse result record.
	 * @throws IOException If the spec file cannot be read.
	 */
	public static Result parse(Path spec) throws
			Errors.ModuleResolutionFailure,
			Errors.CircularModuleDependencyFailure,
			Errors.SyntaxParsingFailure,
			Errors.SemanticCheckingFailure,
			Errors.LevelCheckingFailure {
		InputStream sourceCode;
		try {
			sourceCode = new FileInputStream(spec.toFile());
		} catch (IOException e) {
			throw new Errors.ModuleResolutionFailure(spec.toString());
		}
		ExternalModuleTable deps = new ExternalModuleTable();
		Deque<String> pendingModules = new ArrayDeque<String>();
		Path specDir = spec.getParent();
		Path[] searchPaths = new Path[] { null == specDir ? Path.of(".") : specDir };
		Result result = parse(sourceCode, deps, pendingModules, searchPaths);
		result.dependencies.setRootModule(result.semanticTree);
		return result;
	}
	
	/**
	 * Parses spec, transitively resolves dependencies, then runs semantic
	 * analysis & level-checking on it; this function is called recursively
	 * from dependencies as they are resolved.
	 * @param sourceCode The source module, as an input stream.
	 * @param deps A table of resolved dependencies.
	 * @param pendingModules Modules with yet-unresolved dependencies.
	 * @param moduleSearchPaths Directories in which to look for modules.
	 * @return A parse result record.
	 */
	private static Result parse(
			InputStream sourceCode,
			ExternalModuleTable deps,
			Deque<String> pendingModules,
			Path[] moduleSearchPaths
		) throws
			Errors.ModuleResolutionFailure,
			Errors.CircularModuleDependencyFailure,
			Errors.SyntaxParsingFailure,
			Errors.SemanticCheckingFailure,
			Errors.LevelCheckingFailure {
		TreeNode syntaxTree = parseSyntax(sourceCode);
		resolveDependencies(syntaxTree, deps, pendingModules, moduleSearchPaths);
		Result result = checkSemantic(syntaxTree, deps);
		checkLevel(result.semanticTree);
		return result;
	}
	
	/**
	 * Parses spec syntax; does not resolve references or anything.
	 * @param sourceCode The spec source code, as an input stream.
	 * @return The root node of the spec's syntax tree.
	 */
	private static TreeNode parseSyntax(
		InputStream sourceCode
	) throws Errors.SyntaxParsingFailure {
		TLAplusParser parser = new TLAplusParser(sourceCode, StandardCharsets.UTF_8.name());
		try {
			return parser.CompilationUnit();
		} catch (ParseException e) {
			throw new Errors.SyntaxParsingFailure(e);
		}
	}

	/**
	 * Resolves dependencies of the current module in a depth-first fashion.
	 * Circular dependencies are detected by keeping track of the modules
	 * that are in the process of having their dependencies resolved. The
	 * resolved dependencies are added to the deps table, in place. This also
	 * ensures dependencies are not resolved multiple times.
	 * @param syntaxTree The syntax parse tree.
	 * @param deps Table of resolved dependencies.
	 * @param pendingModules Modules with yet-unresolved dependencies.
	 * @param moduleSearchPaths Directories in which to look for modules.
	 */
	private static void resolveDependencies(
			TreeNode syntaxTree,
			ExternalModuleTable deps,
			Deque<String> pendingModules,
			Path[] moduleSearchPaths
		) throws
			Errors.ModuleResolutionFailure,
			Errors.CircularModuleDependencyFailure,
			Errors.SyntaxParsingFailure,
			Errors.SemanticCheckingFailure,
			Errors.LevelCheckingFailure {
		// Index 0 is the module header: ---- MODULE ModName ----
		String moduleName = syntaxTree.heirs()[0].heirs()[1].getImage();
		pendingModules.addFirst(moduleName);

		// Index 1 is the EXTENDS statement: EXTENDS Naturals, Sequences
		TreeNode extensions = syntaxTree.heirs()[1];
		// The zeroeth element of the heirs is the EXTENDS keyword itself
		for (int i = 1; i < extensions.heirs().length; i++) {
			TreeNode extension = extensions.heirs()[i];
			String depName = extension.getImage();
			if (pendingModules.contains(depName)) {
				throw new Errors.CircularModuleDependencyFailure(pendingModules, depName, moduleName);
			}
			if (null == deps.getModuleNode(depName)) {
				InputStream depSourceCode = resolveModule(depName, moduleSearchPaths);
				Result result = parse(depSourceCode, deps, pendingModules, moduleSearchPaths);
				deps.put(UniqueString.of(depName), null, result.semanticTree);
			}
		}

		pendingModules.pop();
	}

	/**
	 * Find the module with the given name. Currently only resolves standard
	 * modules that are embedded in the tla2tools jar.
	 * @param moduleName The name of the module to resolve.
	 * @return An input stream of the module source code.
	 * @param moduleSearchPaths Directories in which to look for modules.
	 */
	private static InputStream resolveModule(
		String moduleName,
		Path[] moduleSearchPaths
	) throws Errors.ModuleResolutionFailure {
		if (Constants.isStandardModule(moduleName)) {
			String resourcePath = String.format("/tla2sany/StandardModules/%s%s", moduleName, Constants.TLA_FILE_SUFFIX);
			InputStream module = Parser.class.getResourceAsStream(resourcePath);
			if (null == module) {
				throw new RuntimeException("ERROR: Missing standard module " + moduleName);
			}
			return module;
		}

		for (Path dir : moduleSearchPaths) {
			try {
				Path modulePath = dir.resolve(moduleName + Constants.TLA_FILE_SUFFIX);
				return new FileInputStream(modulePath.toFile());
			} catch (InvalidPathException e) {
				throw new Errors.ModuleResolutionFailure(e);
			} catch (IOException e) {
				// Module does not exist here; continue.
				continue;
			}
		}
		
		throw new Errors.ModuleResolutionFailure(moduleName, moduleSearchPaths);
	}

	/**
	 * Derives a semantic graph from a spec's syntax tree. Resolves all
	 * imports and identifier references.
	 * @param parseTree The root node of the spec's syntax tree.
	 * @param deps Parsed modules this spec can depend upon.
	 * @return A parse result record.
	 */
	private static Result checkSemantic(
		TreeNode parseTree,
		ExternalModuleTable deps
	) throws Errors.SemanticCheckingFailure {
		Context.reInit();
		tla2sany.semantic.Errors log = new tla2sany.semantic.Errors();
		Generator gen = new Generator(deps, log);
		ModuleNode semanticTree = null;
		try {
			semanticTree = gen.generate(parseTree);
		} catch (AbortException e) {
			throw new Errors.SemanticCheckingFailure(e);
		}
		if (log.isFailure() || null == semanticTree) {
			throw new Errors.SemanticCheckingFailure(log);
		}
		return new Result(parseTree, deps, gen, semanticTree, log);
	}
	
	/**
	 * Performs level-checking analysis on a spec's semantic graph.
	 * @param semanticTree The root node of the spec's semantic graph.
	 */
	private static void checkLevel(ModuleNode semanticTree) throws
			Errors.LevelCheckingFailure {
		if (!semanticTree.levelCheck(1)) {
		}
	}
}