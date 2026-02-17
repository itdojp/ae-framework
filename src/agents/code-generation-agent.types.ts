/**
 * Code Generation Agent type definitions
 * Extracted to keep implementation focused and reviewable.
 */

export interface CodeGenerationRequest {
  tests: TestFile[];
  specifications?: Specification;
  architecture?: ArchitecturePattern;
  language: 'typescript' | 'javascript' | 'python' | 'go' | 'rust' | 'elixir';
  framework?: string;
  style?: CodingStyle;
}

export interface TestFile {
  path: string;
  content: string;
  type: 'unit' | 'integration' | 'e2e';
}

export interface Specification {
  openapi?: string;
  tla?: string;
  contracts?: Contract[];
  requirements?: string[];
}

export interface Contract {
  name: string;
  preconditions: string[];
  postconditions: string[];
  invariants: string[];
}

export interface ArchitecturePattern {
  pattern: 'mvc' | 'hexagonal' | 'clean' | 'ddd' | 'microservice';
  layers?: Layer[];
  dependencies?: Dependency[];
}

export interface Layer {
  name: string;
  responsibilities: string[];
  allowedDependencies: string[];
}

export interface Dependency {
  from: string;
  to: string;
  type: 'uses' | 'implements' | 'extends';
}

export interface CodingStyle {
  naming: 'camelCase' | 'snake_case' | 'PascalCase';
  indentation: 'spaces' | 'tabs';
  indentSize?: number;
  maxLineLength?: number;
  preferConst?: boolean;
  preferArrowFunctions?: boolean;
}

export interface GeneratedCode {
  files: CodeFile[];
  structure: ProjectStructure;
  dependencies: string[];
  testResults: TestResult[];
  coverage: number;
  suggestions: string[];
}

export interface CodeFile {
  path: string;
  content: string;
  purpose: string;
  tests: string[];
}

export interface ProjectStructure {
  directories: string[];
  entryPoint: string;
  configFiles: ConfigFile[];
}

export interface ConfigFile {
  name: string;
  content: string;
  purpose: string;
}

export interface TestResult {
  test: string;
  status: 'passing' | 'failing' | 'pending';
  error?: string;
}


export interface TestAnalysis {
  functions: string[];
  classes: string[];
  expectedBehaviors: string[];
}

export interface DatabaseSchema {
  tables: Table[];
  relations: Relation[];
}

export interface Table {
  name: string;
  columns: Column[];
  indexes: Index[];
}

export interface Column {
  name: string;
  type: string;
  nullable: boolean;
  primary?: boolean;
  unique?: boolean;
}

export interface Index {
  name: string;
  columns: string[];
  unique: boolean;
}

export interface Relation {
  from: string;
  to: string;
  type: 'one-to-one' | 'one-to-many' | 'many-to-many';
}

export interface PerformanceImprovement {
  location: string;
  type: string;
  description: string;
  impact: 'high' | 'medium' | 'low';
}

export interface Benchmark {
  name: string;
  before: number;
  after: number;
  improvement: number;
}

export interface RefactoringChange {
  type: string;
  location: string;
  description: string;
}

export interface CodeMetrics {
  complexity: number;
  maintainability: number;
  duplication: number;
  testCoverage: number;
}
