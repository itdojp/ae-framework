/**
 * Failure Artifact Factory
 * Phase 2.1: Factory for creating standardized failure artifacts
 */

import type { v4 as uuidv4 } from 'uuid';
import { 
  FailureArtifact, 
  FailureCategory, 
  CodeLocation,
  FailureArtifactSchema 
} from './types.js';

export class FailureArtifactFactory {
  /**
   * Create failure artifact from a runtime error
   */
  static fromError(
    error: Error,
    location?: CodeLocation,
    context?: Record<string, any>
  ): FailureArtifact {
    const artifact: FailureArtifact = {
      id: uuidv4(),
      title: `Runtime Error: ${error.name}`,
      description: error.message || 'Unknown runtime error occurred',
      severity: 'major',
      category: 'runtime_error',
      location,
      context: {
        environment: process.env.NODE_ENV || 'development',
        nodeVersion: process.version,
        timestamp: new Date().toISOString(),
        ...context
      },
      evidence: {
        stackTrace: error.stack,
        errorType: error.constructor.name,
        errorMessage: error.message,
        logs: [error.message],
        metrics: {},
        dependencies: [],
        relatedFiles: []
      },
      suggestedActions: [],
      relatedArtifacts: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['runtime', 'error', error.name.toLowerCase()],
        source: 'error_handler'
      }
    };

    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Create failure artifact from test failure
   */
  static fromTestFailure(
    testName: string,
    expected: any,
    actual: any,
    location?: CodeLocation,
    testOutput?: string
  ): FailureArtifact {
    const artifact: FailureArtifact = {
      id: uuidv4(),
      title: `Test Failure: ${testName}`,
      description: `Test "${testName}" failed. Expected ${JSON.stringify(expected)}, but got ${JSON.stringify(actual)}`,
      severity: 'major',
      category: 'test_failure',
      location,
      context: {
        environment: process.env.NODE_ENV || 'test',
        nodeVersion: process.version,
        timestamp: new Date().toISOString(),
        phase: 'test'
      },
      evidence: {
        testOutput,
        logs: [`Test failed: ${testName}`],
        metrics: {
          expected: typeof expected === 'number' ? expected : 0,
          actual: typeof actual === 'number' ? actual : 0
        },
        dependencies: [],
        relatedFiles: []
      },
      suggestedActions: [],
      relatedArtifacts: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['test', 'failure', 'assertion'],
        source: 'test_runner'
      }
    };

    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Create failure artifact from TypeScript compilation error
   */
  static fromTypeError(
    message: string,
    filePath: string,
    line: number,
    column: number,
    sourceCode?: string
  ): FailureArtifact {
    const artifact: FailureArtifact = {
      id: uuidv4(),
      title: `Type Error: ${filePath}:${line}:${column}`,
      description: message,
      severity: 'major',
      category: 'type_error',
      location: {
        filePath,
        startLine: line,
        endLine: line,
        startColumn: column,
        endColumn: column
      },
      context: {
        environment: 'build',
        nodeVersion: process.version,
        timestamp: new Date().toISOString(),
        phase: 'code'
      },
      evidence: {
        errorMessage: message,
        sourceCode,
        logs: [`TypeScript error: ${message}`],
        metrics: {},
        dependencies: [],
        relatedFiles: []
      },
      suggestedActions: [],
      relatedArtifacts: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['typescript', 'type', 'compilation'],
        source: 'typescript_compiler'
      }
    };

    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Create failure artifact from contract violation
   */
  static fromContractViolation(
    contractName: string,
    violationType: 'input' | 'output' | 'schema',
    actualData: any,
    location?: CodeLocation,
    expectedSchema?: string
  ): FailureArtifact {
    const artifact: FailureArtifact = {
      id: uuidv4(),
      title: `Contract Violation: ${contractName}`,
      description: `${violationType} contract violation in ${contractName}. Data does not conform to expected schema.`,
      severity: 'major',
      category: 'contract_violation',
      location,
      context: {
        environment: process.env.NODE_ENV || 'runtime',
        nodeVersion: process.version,
        timestamp: new Date().toISOString()
      },
      evidence: {
        errorMessage: `Contract violation: ${violationType}`,
        logs: [
          `Contract: ${contractName}`,
          `Violation type: ${violationType}`,
          `Actual data: ${JSON.stringify(actualData, null, 2)}`
        ],
        metrics: {
          dataSize: JSON.stringify(actualData).length,
          fieldCount: typeof actualData === 'object' ? Object.keys(actualData || {}).length : 0
        },
        dependencies: [],
        relatedFiles: []
      },
      suggestedActions: [],
      relatedArtifacts: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['contract', 'validation', violationType, contractName],
        source: 'conformance_guard',
        environment: {
          contractName,
          violationType,
          expectedSchema: expectedSchema || 'unknown'
        }
      }
    };

    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Create failure artifact from build error
   */
  static fromBuildError(
    message: string,
    command: string,
    exitCode: number,
    buildOutput: string,
    workingDirectory?: string
  ): FailureArtifact {
    const artifact: FailureArtifact = {
      id: uuidv4(),
      title: `Build Error: ${command}`,
      description: `Build command "${command}" failed with exit code ${exitCode}. ${message}`,
      severity: exitCode === 1 ? 'major' : 'critical',
      category: 'build_error',
      context: {
        environment: 'build',
        nodeVersion: process.version,
        timestamp: new Date().toISOString(),
        command,
        workingDirectory: workingDirectory || process.cwd(),
        phase: 'code'
      },
      evidence: {
        errorMessage: message,
        buildOutput,
        logs: buildOutput.split('\n').filter(line => line.trim()),
        metrics: {
          exitCode,
          outputLines: buildOutput.split('\n').length
        },
        dependencies: [],
        relatedFiles: []
      },
      suggestedActions: [],
      relatedArtifacts: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['build', 'compilation', 'failure'],
        source: 'build_system',
        environment: {
          command,
          exitCode: exitCode.toString()
        }
      }
    };

    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Create failure artifact from lint error
   */
  static fromLintError(
    rule: string,
    message: string,
    filePath: string,
    line: number,
    column: number,
    severity: 'error' | 'warning' = 'error',
    sourceCode?: string
  ): FailureArtifact {
    const artifact: FailureArtifact = {
      id: uuidv4(),
      title: `Lint ${severity}: ${rule}`,
      description: `ESLint ${severity} in ${filePath}:${line}:${column} - ${message}`,
      severity: severity === 'error' ? 'minor' : 'info',
      category: 'lint_error',
      location: {
        filePath,
        startLine: line,
        endLine: line,
        startColumn: column,
        endColumn: column
      },
      context: {
        environment: 'development',
        nodeVersion: process.version,
        timestamp: new Date().toISOString(),
        phase: 'code'
      },
      evidence: {
        errorMessage: message,
        sourceCode,
        logs: [`ESLint ${severity}: ${rule} - ${message}`],
        metrics: {},
        dependencies: [],
        relatedFiles: []
      },
      suggestedActions: [],
      relatedArtifacts: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['eslint', 'code-quality', rule, severity],
        source: 'eslint',
        environment: {
          rule,
          severity
        }
      }
    };

    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Create failure artifact from dependency issue
   */
  static fromDependencyIssue(
    packageName: string,
    issueType: 'missing' | 'version_mismatch' | 'security_vulnerability' | 'deprecated',
    message: string,
    currentVersion?: string,
    requiredVersion?: string
  ): FailureArtifact {
    const artifact: FailureArtifact = {
      id: uuidv4(),
      title: `Dependency Issue: ${packageName}`,
      description: `${issueType} issue with package "${packageName}": ${message}`,
      severity: issueType === 'security_vulnerability' ? 'critical' : 'major',
      category: 'dependency_issue',
      context: {
        environment: process.env.NODE_ENV || 'development',
        nodeVersion: process.version,
        timestamp: new Date().toISOString()
      },
      evidence: {
        errorMessage: message,
        logs: [`Dependency issue: ${packageName} - ${issueType}`],
        dependencies: [packageName],
        metrics: {},
        relatedFiles: []
      },
      suggestedActions: [],
      relatedArtifacts: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['dependency', 'package', issueType, packageName],
        source: 'package_manager',
        environment: {
          packageName,
          issueType,
          currentVersion: currentVersion || 'unknown',
          requiredVersion: requiredVersion || 'unknown'
        }
      }
    };

    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Create failure artifact from performance issue
   */
  static fromPerformanceIssue(
    metric: string,
    threshold: number,
    actual: number,
    location?: CodeLocation,
    context?: Record<string, any>
  ): FailureArtifact {
    const artifact: FailureArtifact = {
      id: uuidv4(),
      title: `Performance Issue: ${metric}`,
      description: `Performance threshold exceeded for ${metric}. Expected <= ${threshold}, but got ${actual}`,
      severity: actual > threshold * 2 ? 'critical' : 'major',
      category: 'performance_issue',
      location,
      context: {
        environment: process.env.NODE_ENV || 'development',
        nodeVersion: process.version,
        timestamp: new Date().toISOString(),
        phase: 'verify',
        ...context
      },
      evidence: {
        logs: [`Performance issue: ${metric} = ${actual} (threshold: ${threshold})`],
        metrics: {
          [metric]: actual,
          [`${metric}_threshold`]: threshold,
          [`${metric}_ratio`]: actual / threshold
        },
        dependencies: [],
        relatedFiles: []
      },
      suggestedActions: [],
      relatedArtifacts: [],
      metadata: {
        createdAt: new Date().toISOString(),
        updatedAt: new Date().toISOString(),
        version: '1.0.0',
        tags: ['performance', metric, 'threshold'],
        source: 'performance_monitor',
        environment: {
          metric,
          threshold: threshold.toString(),
          actual: actual.toString()
        }
      }
    };

    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Validate and enrich an existing failure artifact
   */
  static validate(artifact: any): FailureArtifact {
    return FailureArtifactSchema.parse(artifact);
  }

  /**
   * Create a collection of related failure artifacts
   */
  static createRelatedGroup(
    artifacts: Partial<FailureArtifact>[],
    groupId: string = uuidv4()
  ): FailureArtifact[] {
    const processedArtifacts: FailureArtifact[] = [];
    
    for (const partialArtifact of artifacts) {
      const artifact = FailureArtifactSchema.parse({
        id: uuidv4(),
        ...partialArtifact,
        metadata: {
          createdAt: new Date().toISOString(),
          updatedAt: new Date().toISOString(),
          version: '1.0.0',
          tags: [],
          source: 'cegis_system',
          ...partialArtifact.metadata,
          environment: {
            groupId,
            ...partialArtifact.metadata?.environment
          }
        }
      });
      
      processedArtifacts.push(artifact);
    }
    
    // Link all artifacts in the group
    const artifactIds = processedArtifacts.map(a => a.id);
    processedArtifacts.forEach(artifact => {
      artifact.relatedArtifacts = artifactIds.filter(id => id !== artifact.id);
    });
    
    return processedArtifacts;
  }
}