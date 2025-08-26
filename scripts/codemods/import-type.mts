import { Project, SyntaxKind, ImportDeclaration, Node } from 'ts-morph';
import { glob } from 'glob';

interface ImportUsageAnalysis {
  hasTypeOnlyUsage: boolean;
  hasValueUsage: boolean;
  usedIdentifiers: Set<string>;
}

function analyzeImportUsage(
  importDeclaration: ImportDeclaration,
  sourceFile: any
): ImportUsageAnalysis {
  const analysis: ImportUsageAnalysis = {
    hasTypeOnlyUsage: false,
    hasValueUsage: false,
    usedIdentifiers: new Set(),
  };

  // Get all imported identifiers
  const namedImports = importDeclaration.getNamedImports();
  const defaultImport = importDeclaration.getDefaultImport();
  const namespaceImport = importDeclaration.getNamespaceImport();

  const allImportedNames = new Set<string>();

  // Collect all imported names
  namedImports.forEach(namedImport => {
    const name = namedImport.getName();
    allImportedNames.add(name);
    const aliasNode = namedImport.getAliasNode();
    if (aliasNode) {
      allImportedNames.add(aliasNode.getText());
    }
  });

  if (defaultImport) {
    allImportedNames.add(defaultImport.getText());
  }

  if (namespaceImport) {
    allImportedNames.add(namespaceImport.getText());
  }

  // Find all usages in the source file
  sourceFile.forEachDescendant((node: Node) => {
    if (Node.isIdentifier(node)) {
      const identifierName = node.getText();
      
      if (allImportedNames.has(identifierName)) {
        analysis.usedIdentifiers.add(identifierName);
        
        // Check if this identifier is used in a type context
        const parent = node.getParent();
        const grandParent = parent?.getParent();
        
        const isInTypeContext = 
          // Type annotations: foo: Type
          (Node.isTypeReference(parent)) ||
          // Generic parameters: Array<Type>
          (Node.isTypeReference(grandParent)) ||
          // Interface extends: extends Type
          (parent?.getKind() === SyntaxKind.ExpressionWithTypeArguments) ||
          // Type aliases: type Foo = Type
          (parent?.getKind() === SyntaxKind.TypeAliasDeclaration) ||
          // Function return types: (): Type
          (parent?.getKind() === SyntaxKind.TypeReference) ||
          // Variable type annotations: const x: Type
          (parent?.getKind() === SyntaxKind.TypeAnnotation) ||
          // Parameter type annotations: (param: Type)
          (grandParent?.getKind() === SyntaxKind.Parameter && parent?.getKind() === SyntaxKind.TypeReference) ||
          // Property type annotations: prop: Type
          (grandParent?.getKind() === SyntaxKind.PropertySignature) ||
          // As expressions: x as Type  
          (parent?.getKind() === SyntaxKind.AsExpression) ||
          // Type predicates: is Type
          (parent?.getKind() === SyntaxKind.TypePredicate) ||
          // Mapped types and utility types
          (parent?.getKind() === SyntaxKind.MappedType) ||
          // Template literal types
          (parent?.getKind() === SyntaxKind.TemplateLiteralType);

        if (isInTypeContext) {
          analysis.hasTypeOnlyUsage = true;
        } else {
          // Check if it's used in a runtime context
          const isRuntimeUsage =
            // Function calls: fn()
            (parent?.getKind() === SyntaxKind.CallExpression) ||
            // Property access: obj.prop
            (parent?.getKind() === SyntaxKind.PropertyAccessExpression) ||
            // Element access: obj[key]
            (parent?.getKind() === SyntaxKind.ElementAccessExpression) ||
            // Variable assignment: x = value
            (parent?.getKind() === SyntaxKind.BinaryExpression) ||
            // Return statements: return value
            (parent?.getKind() === SyntaxKind.ReturnStatement) ||
            // Array/object literals: [value] or {key: value}
            (parent?.getKind() === SyntaxKind.ArrayLiteralExpression) ||
            (parent?.getKind() === SyntaxKind.ObjectLiteralExpression) ||
            // New expressions: new Constructor()
            (parent?.getKind() === SyntaxKind.NewExpression) ||
            // instanceof checks: x instanceof Type
            (parent?.getKind() === SyntaxKind.BinaryExpression && 
             parent.getOperatorToken().getKind() === SyntaxKind.InstanceOfKeyword);

          if (isRuntimeUsage || !isInTypeContext) {
            analysis.hasValueUsage = true;
          }
        }
      }
    }
  });

  return analysis;
}

function shouldConvertToTypeImport(analysis: ImportUsageAnalysis): boolean {
  // Convert to type import only if:
  // 1. It has type-only usage AND no value usage, OR
  // 2. It has no usage at all (dead import - still convert for consistency)
  return analysis.hasTypeOnlyUsage && !analysis.hasValueUsage;
}

async function processFile(filePath: string, project: Project): Promise<boolean> {
  console.log(`Processing: ${filePath}`);
  
  const sourceFile = project.addSourceFileAtPath(filePath);
  let modified = false;

  const importDeclarations = sourceFile.getImportDeclarations();

  for (const importDeclaration of importDeclarations) {
    // Skip if already a type-only import
    if (importDeclaration.isTypeOnly()) {
      continue;
    }

    // Skip relative imports from .js files (likely runtime dependencies)
    const moduleSpecifier = importDeclaration.getModuleSpecifierValue();
    if (moduleSpecifier.endsWith('.js') || moduleSpecifier.endsWith('.mjs')) {
      continue;
    }

    const analysis = analyzeImportUsage(importDeclaration, sourceFile);
    
    if (shouldConvertToTypeImport(analysis)) {
      // Convert to type-only import
      const moduleSpecifier = importDeclaration.getModuleSpecifierValue();
      const namedImports = importDeclaration.getNamedImports();
      const defaultImport = importDeclaration.getDefaultImport();
      const namespaceImport = importDeclaration.getNamespaceImport();

      // Build new import statement
      let newImportText = 'import type ';
      
      if (defaultImport && namedImports.length > 0) {
        // Mixed default + named imports: import type Foo, { Bar } from 'module'
        newImportText += `${defaultImport.getText()}, { ${namedImports.map(n => n.getText()).join(', ')} }`;
      } else if (defaultImport) {
        // Default import only: import type Foo from 'module'
        newImportText += defaultImport.getText();
      } else if (namespaceImport) {
        // Namespace import: import type * as Foo from 'module'
        newImportText += `* as ${namespaceImport.getText()}`;
      } else if (namedImports.length > 0) {
        // Named imports only: import type { Foo, Bar } from 'module'
        newImportText += `{ ${namedImports.map(n => n.getText()).join(', ')} }`;
      } else {
        // Side-effect import - skip
        continue;
      }
      
      newImportText += ` from '${moduleSpecifier}';`;
      
      // Replace the import
      importDeclaration.replaceWithText(newImportText);
      modified = true;
      
      console.log(`  ✓ Converted: ${importDeclaration.getText().trim()} -> ${newImportText}`);
    }
  }

  if (modified) {
    sourceFile.saveSync();
  }

  // Clean up to avoid memory issues
  project.removeSourceFile(sourceFile);
  
  return modified;
}

async function main() {
  console.log('[codemod:import-type] Starting import type codemod...');
  
  const project = new Project({
    tsConfigFilePath: 'tsconfig.json',
  });

  // Find all TypeScript files in src/
  const files = await glob('src/**/*.ts', { 
    ignore: ['**/*.d.ts', '**/*.test.ts', '**/*.spec.ts'] 
  });
  
  console.log(`Found ${files.length} TypeScript files to process`);
  
  let totalModified = 0;
  let processedCount = 0;

  for (const file of files) {
    try {
      const wasModified = await processFile(file, project);
      if (wasModified) {
        totalModified++;
      }
      processedCount++;
      
      if (processedCount % 10 === 0) {
        console.log(`Progress: ${processedCount}/${files.length} files processed`);
      }
    } catch (error) {
      console.error(`Error processing ${file}:`, error);
    }
  }

  console.log('\n[codemod:import-type] Summary:');
  console.log(`  Files processed: ${processedCount}`);
  console.log(`  Files modified: ${totalModified}`);
  console.log(`  Files unchanged: ${processedCount - totalModified}`);
  
  if (totalModified > 0) {
    console.log('\n✓ Import type codemod completed successfully');
    console.log('Run `npm run build` to verify changes compile correctly');
  } else {
    console.log('\n✓ No files needed modification');
  }
}

main().catch(error => {
  console.error('[codemod:import-type] Fatal error:', error);
  process.exit(1);
});