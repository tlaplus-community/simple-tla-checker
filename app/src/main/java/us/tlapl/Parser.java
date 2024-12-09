package us.tlapl;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import tla2sany.semantic.ModuleNode;
import tla2sany.st.TreeNode;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.net.URISyntaxException;
import java.net.URL;
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
		Map<String, ModuleNode> deps = new HashMap<String, ModuleNode>();
		return new Model(parse(spec, deps));
	}
	
	private static ModuleNode parse(Path spec, Map<String, ModuleNode> deps) throws IOException {
		byte[] sourceCode = getSourceCode(spec);
		TreeNode syntaxTree = parseSyntax(sourceCode);
		resolveDependencies(syntaxTree, deps);
		ModuleNode semanticTree = checkSemantic(syntaxTree, deps);
		boolean levelCheck = checkLevel(semanticTree);
		assert levelCheck;
		return semanticTree;
	}
	
	/**
	 * Get spec source text as UTF-8 bytes.
	 * @param spec The path to the spec.
	 * @return The bytes comprising the source text.
	 * @throws IOException If spec file cannot be read.
	 */
	private static byte[] getSourceCode(Path spec) throws IOException {
		return Files.readAllBytes(spec);
	}

	/**
	 * Parses spec syntax; does not resolve references or anything.
	 * @param sourceCode The spec source code, as bytes.
	 * @return The root node of the spec's syntax tree.
	 */
	private static TreeNode parseSyntax(byte[] sourceCode) {
		InputStream inputStream = new ByteArrayInputStream(sourceCode);
		TLAplusParser parser = new TLAplusParser(inputStream, StandardCharsets.UTF_8.name());
		boolean result = parser.parse();
		assert result;
		TreeNode root = parser.rootNode();
		assert null != root;
		return root;
	}

	private static void resolveDependencies(TreeNode syntaxTree, Map<String, ModuleNode> deps) throws IOException {
		// Index 0 is the module header, index 1 is the EXTENDS statements
		TreeNode extensions = syntaxTree.heirs()[1];
		for (TreeNode extension : extensions.heirs()) {
			String moduleName = extension.getImage();
			if (!deps.containsKey(moduleName)) {
				Path modulePath = resolveModuleName(moduleName);
				deps.put(moduleName, parse(modulePath, deps));
			}
		}
	}

	private static Path resolveModuleName(String moduleName) throws IOException {
		String resourcePath = "/tla2sany/StandardModules/" + moduleName + ".tla";
		URL resource = Parser.class.getResource(resourcePath);
		if (null == resource) {
			throw new IOException("Unable to find standard module " + moduleName);
		}
		try {
			return Paths.get(resource.toURI());
		} catch (URISyntaxException e) {
			// This should never happen.
			return null;
		}
	}

	/**
	 * Derives a semantic graph from a spec's syntax tree. Resolves all
	 * imports and identifier references.
	 * @param parseTree The root node of the spec's syntax tree.
	 * @param deps Parsed modules this spec can depend upon.
	 * @return The root node of the spec's semantic graph.
	 */
	private static ModuleNode checkSemantic(TreeNode parseTree, Map<String, ModuleNode> deps) {
		Context.reInit();
		Errors log = new Errors();
		// TODO: convert deps to ExternalModuleTable
		// Need to figure out contexts
		Generator gen = new Generator(null, log);
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