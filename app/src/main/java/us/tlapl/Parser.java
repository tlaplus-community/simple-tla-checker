package us.tlapl;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;

import tla2sany.semantic.ModuleNode;
import tla2sany.st.TreeNode;
import util.UniqueString;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Context;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.Generator;
import tla2sany.semantic.SemanticNode;

/**
 * Get from spec filepath to semantic graph.
 */
public class Parser {

	/**
	 * Reads a spec source file, parses it, then runs semantic analysis and
	 * level-checking on it.
	 * @param spec Path to the spec source file.
	 * @return The root node of the spec's semantic graph.
	 * @throws IOException If the spec file cannot be read.
	 */
	public static Model parse(Path spec) throws IOException {
		byte[] sourceCodeBytes = Files.readAllBytes(spec);
		InputStream sourceCode = new ByteArrayInputStream(sourceCodeBytes);
		ExternalModuleTable deps = new ExternalModuleTable();
		ModuleNode semanticTree = parse(sourceCode, deps, new HashSet<String>());
		deps.setRootModule(semanticTree);
		return new Model(semanticTree, deps);
	}
	
	/**
	 * Parses spec, transitively resolves dependencies, then runs semantic
	 * analysis & level-checking on it; this function is called recursively
	 * from dependencies as they are resolved.
	 * @param sourceCode The source module, as an input stream.
	 * @param deps A table of resolved dependencies.
	 * @param pendingModules Modules with yet-unresolved dependencies.
	 * @return The root node of the spec's semantic graph.
	 * @throws IOException If a module dependency cannot be resolved.
	 */
	private static ModuleNode parse(
		InputStream sourceCode,
		ExternalModuleTable deps,
		Set<String> pendingModules
	) throws IOException {
		TreeNode syntaxTree = parseSyntax(sourceCode);
		resolveDependencies(syntaxTree, deps, pendingModules);
		ModuleNode semanticTree = checkSemantic(syntaxTree, deps);
		boolean levelCheck = checkLevel(semanticTree);
		assert levelCheck;
		return semanticTree;
	}
	
	/**
	 * Parses spec syntax; does not resolve references or anything.
	 * @param sourceCode The spec source code, as an input stream.
	 * @return The root node of the spec's syntax tree.
	 */
	private static TreeNode parseSyntax(InputStream sourceCode) {
		TLAplusParser parser = new TLAplusParser(sourceCode, StandardCharsets.UTF_8.name());
		boolean result = parser.parse();
		assert result;
		TreeNode root = parser.rootNode();
		assert null != root;
		return root;
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
	 * @throws IOException If a module dependency cannot be resolved.
	 */
	private static void resolveDependencies(
		TreeNode syntaxTree,
		ExternalModuleTable deps,
		Set<String> pendingModules
	) throws IOException {
		// Index 0 is the module header: ---- MODULE ModName ----
		String moduleName = syntaxTree.heirs()[0].heirs()[1].getImage();
		pendingModules.add(moduleName);

		// Index 1 is the EXTENDS statement: EXTENDS Naturals, Sequences
		TreeNode extensions = syntaxTree.heirs()[1];
		// The zeroeth element of the heirs is the EXTENDS keyword itself
		for (int i = 1; i < extensions.heirs().length; i++) {
			TreeNode extension = extensions.heirs()[i];
			String depName = extension.getImage();
			if (pendingModules.contains(depName)) {
				throw new IllegalArgumentException(
					"Circular dependency: module " + moduleName + " depends on " + depName + ", which in turn depends on it."
				);
			}
			if (null == deps.getModuleNode(depName)) {
				InputStream depSourceCode = resolveModule(depName);
				ModuleNode depSemanticTree = parse(depSourceCode, deps, pendingModules);
				deps.put(UniqueString.of(depName), null, depSemanticTree);
			}
		}

		pendingModules.remove(moduleName);
	}

	/**
	 * Find the module with the given name. Currently only resolves standard
	 * modules that are embedded in the tla2tools jar.
	 * @param moduleName The name of the module to resolve.
	 * @return An input stream of the module source code.
	 * @throws IOException If the module could not be found.
	 */
	private static InputStream resolveModule(String moduleName) throws IOException {
		String resourcePath = "/tla2sany/StandardModules/" + moduleName + ".tla";
		InputStream module = Parser.class.getResourceAsStream(resourcePath);
		if (null == module) {
			throw new IOException("Unable to find module " + moduleName);
		}
		return module;
	}

	/**
	 * Derives a semantic graph from a spec's syntax tree. Resolves all
	 * imports and identifier references.
	 * @param parseTree The root node of the spec's syntax tree.
	 * @param deps Parsed modules this spec can depend upon.
	 * @return The root node of the spec's semantic graph.
	 */
	private static ModuleNode checkSemantic(TreeNode parseTree, ExternalModuleTable deps) {
		Context.reInit();
		Errors log = new Errors();
		Generator gen = new Generator(deps, log);
		SemanticNode.setError(log);
		ModuleNode semanticTree = null;
		try {
			semanticTree = gen.generate(parseTree);
		} catch (AbortException e) {
			assert false : e.toString() + log.toString();
		}
		assert log.isSuccess() : log.toString();
		assert null != semanticTree : log.toString();
		return semanticTree;
	}
	
	/**
	 * Performs level-checking analysis on a spec's semantic graph.
	 * @param semanticTree The root node of the spec's semantic graph.
	 * @return Whether level-checking was successful.
	 */
	private static boolean checkLevel(ModuleNode semanticTree) {
		return semanticTree.levelCheck(1);
	}
}