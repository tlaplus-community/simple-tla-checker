package us.tlapl;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import tla2sany.semantic.ModuleNode;
import tla2sany.st.TreeNode;
import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;

import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.Context;
import tla2sany.semantic.Errors;
import tla2sany.semantic.Generator;
import tla2sany.semantic.SemanticNode;

public class Parser {

  public static byte[] getSourceCode(Path spec) throws IOException {
      return Files.readAllBytes(spec);
  }

  public static TreeNode parseSyntax(byte[] sourceCode) {
      InputStream inputStream = new ByteArrayInputStream(sourceCode);
      TLAplusParser parser = new TLAplusParser(inputStream, StandardCharsets.UTF_8.name());
      boolean result = parser.parse();
      assert result;
      TreeNode root = parser.rootNode();
      assert null != root;
      return root;
    }

  private static ModuleNode checkSemantic(TreeNode parseTree) {
      Context.reInit();
      Errors log = new Errors();
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

  private static boolean checkLevel(ModuleNode semanticTree) {
    return semanticTree.levelCheck(1);
  }

  public static ModuleNode parse(Path spec) throws IOException {
      byte[] sourceCode = getSourceCode(spec);
      TreeNode syntaxTree = parseSyntax(sourceCode);
      ModuleNode semanticTree = checkSemantic(syntaxTree);
      boolean levelCheck = checkLevel(semanticTree);
      assert levelCheck;
      return semanticTree;
  }
}