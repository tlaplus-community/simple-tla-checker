package us.tlapl;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Vector;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;

import tla2sany.parser.ParseException;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.Generator;

public class Experiments {

	/**
	 * Adds a new definition to the spec. This will fail if a definition with
	 * the same name already exists.
	 * @param spec Record containing parse trees & artifacts.
	 * @param definition The definition to append.
	 * @throws ParseException If the definition is invalid syntax.
	 */
	public static void addNewDefinition(Parser.Result spec, String definition) throws ParseException {
		String wrappedDef = "---- MODULE Ignore ----\n" + definition + "\n====";
		InputStream sourceCode = new ByteArrayInputStream(wrappedDef.getBytes(StandardCharsets.UTF_8));
		TLAplusParser parser = new TLAplusParser(sourceCode, StandardCharsets.UTF_8.name());
		SyntaxTreeNode parsed = parser.CompilationUnit();
		SyntaxTreeNode parsedDef = parsed.getHeirs()[2].getHeirs()[0];
		processOperator(spec.semanticChecker, spec.semanticTree, parsedDef);
		String defName = parsedDef.getHeirs()[0].getHeirs()[0].getImage();
		resetOpCache(spec.semanticTree);
		OpDefNode checkedDef = spec.semanticTree.getOpDef(defName);
		assert checkedDef.levelCheck(1);
		System.out.println(checkedDef.getSignature());
	}
	
	/**
	 * Generator.processOperator is currently private so hack around that
	 * and call it using reflection.
	 * @param gen The semantic checker generator object.
	 * @param root The root of the existing semantic parse tree.
	 * @param def The new definition to semantically check.
	 */
	private static void processOperator(Generator gen, ModuleNode root, SyntaxTreeNode def) {
		try {
			Method method = gen.getClass().getDeclaredMethod(
					"processOperator",
					TreeNode.class,
					Vector.class,
					ModuleNode.class
				);
			method.setAccessible(true);
			method.invoke(gen, def, null, root);
		} catch (NoSuchMethodException e) {
			System.err.println("Could not find method Generator.processOperator");
			System.exit(1);
		} catch (InvocationTargetException e) {
			System.err.println("Failed to invoke Generator.processOperator");
			System.exit(1);
		} catch (IllegalAccessException e) {
			System.err.println("Failed to access Generator.processOperator");
			System.exit(1);
		}
	}
	
	/**
	 * Calling ModuleNode.getOpDef (or similar) generates & caches a list of
	 * all operators defined in the module. Since we are changing that list
	 * we clear the cache by resetting the value of private field opDefs to
	 * null; the cache was generated during level-checking of the original
	 * module.
	 * @param semanticTree The semantic tree object to clear the cache on.
	 */
	private static void resetOpCache(ModuleNode semanticTree) {
		try {
			Field field = semanticTree.getClass().getDeclaredField("opDefs");
			field.setAccessible(true);
			field.set(semanticTree, null);
		} catch (NoSuchFieldException e) {
			System.err.println("Could not find field ModuleNode.opDefs");
			System.exit(1);
		} catch (IllegalAccessException e) {
			System.err.println("Failed to access field ModuleNode.opDefs");
			System.exit(1);
		}
	}
}