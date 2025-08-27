#!/usr/bin/env tsx
/**
 * TypeScript Import Type Codemod
 * 
 * Transforms regular imports to `import type` when only types are used.
 * Helps with verbatimModuleSyntax compatibility.
 */

import { Project, SyntaxKind, ImportDeclaration, Node } from 'ts-morph';
import { glob } from 'glob';

interface TransformStats {
  filesProcessed: number;
  importsTransformed: number;
  errors: string[];
}

function isTypeOnlyUsage(importDecl: ImportDeclaration): boolean {
  const sourceFile = importDecl.getSourceFile();
  const importedSymbols = new Set<string>();
  
  // Collect imported symbols
  const namedImports = importDecl.getNamedImports();
  namedImports.forEach(namedImport => {
    importedSymbols.add(namedImport.getName());
  });
  
  const defaultImport = importDecl.getDefaultImport();
  if (defaultImport) {
    importedSymbols.add(defaultImport.getText());
  }
  
  const namespaceImport = importDecl.getNamespaceImport();
  if (namespaceImport) {
    importedSymbols.add(namespaceImport.getText());
  }
  
  // Check usage throughout the file
  for (const symbol of importedSymbols) {
    const identifiers = sourceFile.getDescendantsOfKind(SyntaxKind.Identifier)
      .filter(id => id.getText() === symbol && id !== defaultImport && !namedImports.some(ni => ni.getNameNode() === id));
    
    for (const identifier of identifiers) {
      // Skip if it's part of the import declaration itself
      if (identifier.getAncestors().some(ancestor => ancestor === importDecl)) {
        continue;
      }
      
      // Check if used in type-only contexts
      const parent = identifier.getParent();
      if (!parent) continue;
      
      // Type-only contexts
      if (
        parent.getKind() === SyntaxKind.TypeReference ||
        parent.getKind() === SyntaxKind.ExpressionWithTypeArguments ||
        parent.getKind() === SyntaxKind.TypeQuery ||
        Node.isTypeAliasDeclaration(parent) ||
        Node.isInterfaceDeclaration(parent) ||
        Node.isTypeParameterDeclaration(parent)
      ) {
        continue; // This is type-only usage
      }
      
      // Check for type annotations
      if (Node.isTypeNode(parent) || Node.isTypeElement(parent)) {
        continue; // This is type-only usage
      }
      
      // Check if it's in a type assertion
      if (Node.isAsExpression(parent) || Node.isTypeAssertion(parent)) {
        continue; // This is type-only usage
      }
      
      // If we reach here, it's a value usage
      return false;
    }
  }
  
  return true;
}

function transformImportsInFile(filePath: string): number {
  try {
    const project = new Project({
      tsConfigFilePath: 'tsconfig.json',
      skipAddingFilesFromTsConfig: true,
    });
    
    const sourceFile = project.addSourceFileAtPath(filePath);
    const importDeclarations = sourceFile.getImportDeclarations();
    let transformedCount = 0;
    
    for (const importDecl of importDeclarations) {
      // Skip if already a type-only import
      if (importDecl.isTypeOnly()) {
        continue;
      }
      
      // Skip relative imports from same package (likely value imports)
      const moduleSpecifier = importDecl.getModuleSpecifierValue();
      if (moduleSpecifier.startsWith('.')) {
        continue;
      }
      
      // Check if this import is used only in type contexts
      if (isTypeOnlyUsage(importDecl)) {
        importDecl.setIsTypeOnly(true);
        transformedCount++;
        
        console.log(`  ✓ ${filePath}: ${moduleSpecifier} → import type`);
      }
    }
    
    if (transformedCount > 0) {
      sourceFile.saveSync();
    }
    
    return transformedCount;
  } catch (error) {
    console.error(`  ❌ Error processing ${filePath}:`, error);
    return 0;
  }
}

async function main() {
  console.log('🔄 TypeScript Import Type Codemod');
  console.log('Analyzing src/**/*.ts for type-only imports...\n');
  
  const stats: TransformStats = {
    filesProcessed: 0,
    importsTransformed: 0,
    errors: []
  };
  
  try {
    // Find all TypeScript files in src
    const files = await glob('src/**/*.ts', { ignore: ['**/*.d.ts', '**/*.test.ts', '**/*.spec.ts'] });
    
    if (files.length === 0) {
      console.log('No TypeScript files found in src/');
      return;
    }
    
    console.log(`📁 Found ${files.length} TypeScript files to analyze\n`);
    
    for (const file of files) {
      stats.filesProcessed++;
      const transformed = transformImportsInFile(file);
      stats.importsTransformed += transformed;
      
      if (transformed === 0) {
        console.log(`  • ${file}: no changes needed`);
      }
    }
    
    console.log(`\n📊 Summary:`);
    console.log(`  • Files processed: ${stats.filesProcessed}`);
    console.log(`  • Imports transformed: ${stats.importsTransformed}`);
    
    if (stats.errors.length > 0) {
      console.log(`  • Errors: ${stats.errors.length}`);
      stats.errors.forEach(error => console.log(`    - ${error}`));
    }
    
    if (stats.importsTransformed > 0) {
      console.log(`\n✅ Successfully transformed ${stats.importsTransformed} imports to 'import type'`);
      console.log('💡 This should resolve verbatimModuleSyntax violations');
    } else {
      console.log('\n✅ All imports are already correctly typed');
    }
    
  } catch (error) {
    console.error('❌ Failed to run import type codemod:', error);
    process.exit(1);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch(console.error);
}