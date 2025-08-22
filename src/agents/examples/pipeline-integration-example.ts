/**
 * AE Framework Pipeline Integration Example
 * Demonstrates how to use the standardized pipeline for benchmark integration
 */

import { AEFrameworkPipeline, PipelineConfig } from '../pipeline/ae-framework-pipeline.js';
import { IntentAgentAdapter } from '../adapters/intent-agent-adapter.js';
import { 
  RequirementsAgentAdapter, 
  UserStoriesAgentAdapter, 
  ValidationAgentAdapter, 
  DomainModelingAgentAdapter 
} from '../adapters/task-adapters.js';
import { UIUXAgentAdapter } from '../adapters/ui-ux-agent-adapter.js';
import { 
  IntentInput, 
  RequirementSource, 
  ProjectContext 
} from '../interfaces/standard-interfaces.js';

/**
 * Example: Complete AE Framework Pipeline Execution
 */
export async function runCompleteAEFrameworkPipeline() {
  console.log('🚀 Starting AE Framework Pipeline Integration Example');

  // 1. Configure pipeline
  const config: PipelineConfig = {
    projectId: 'example-project-001',
    domain: 'task-management',
    enableParallelProcessing: false,
    validateInputs: true,
    retryFailures: true,
    maxRetries: 2,
    timeoutMs: 300000 // 5 minutes
  };

  // 2. Create pipeline instance
  const pipeline = new AEFrameworkPipeline(config);

  // 3. Register all agent adapters
  pipeline.registerAgent('intent', new IntentAgentAdapter());
  pipeline.registerAgent('requirements', new RequirementsAgentAdapter());
  pipeline.registerAgent('user-stories', new UserStoriesAgentAdapter());
  pipeline.registerAgent('validation', new ValidationAgentAdapter());
  pipeline.registerAgent('domain-modeling', new DomainModelingAgentAdapter());
  pipeline.registerAgent('ui-ux-generation', new UIUXAgentAdapter());

  // 4. Validate pipeline setup
  const validation = pipeline.validatePipeline();
  if (!validation.valid) {
    console.error('❌ Pipeline validation failed:', validation.errors);
    return;
  }
  console.log('✅ Pipeline validation passed');

  // 5. Prepare input for pipeline
  const sources: RequirementSource[] = [
    {
      type: 'text',
      content: `
        We need a task management application that allows teams to collaborate effectively.
        
        Key Requirements:
        - Users must be able to create and assign tasks
        - Tasks should have priorities and due dates
        - Team members should receive notifications about task updates
        - The system should generate progress reports
        - All data must be secure and backed up regularly
        
        Constraints:
        - Must work on mobile and desktop
        - Response time should be under 2 seconds
        - Must integrate with existing authentication system
      `,
      metadata: {
        source: 'Product Requirements Document',
        version: '1.0',
        author: 'Product Manager'
      }
    },
    {
      type: 'conversation',
      content: `
        Stakeholder Interview Summary:
        
        Project Manager: "We need visibility into team workload and project timelines"
        Developer: "The system should be easy to integrate with our existing tools"
        End User: "I want a simple interface that doesn't require training"
      `,
      metadata: {
        source: 'Stakeholder Interviews',
        date: '2024-01-15'
      }
    }
  ];

  const context: ProjectContext = {
    domain: 'task-management',
    organization: 'TechCorp Inc.',
    existingSystem: true,
    constraints: [
      {
        type: 'technical',
        description: 'Must integrate with existing LDAP authentication',
        impact: 'high',
        source: 'IT Security Policy'
      }
    ],
    stakeholders: [
      {
        name: 'Sarah Johnson',
        role: 'Project Manager',
        concerns: ['project visibility', 'team productivity', 'deadline tracking'],
        influenceLevel: 'high'
      },
      {
        name: 'Mike Chen',
        role: 'Software Developer',
        concerns: ['technical feasibility', 'integration complexity', 'maintainability'],
        influenceLevel: 'high'
      },
      {
        name: 'Lisa Wong',
        role: 'End User',
        concerns: ['ease of use', 'training requirements', 'daily workflow'],
        influenceLevel: 'medium'
      }
    ]
  };

  const input: IntentInput = {
    sources,
    context
  };

  try {
    // 6. Execute complete pipeline
    console.log('🔄 Executing AE Framework 6-Phase Pipeline...');
    const result = await pipeline.executePipeline(input);

    // 7. Process results
    if (result.success) {
      console.log('✅ Pipeline execution completed successfully!');
      console.log(`📊 Total Duration: ${result.totalDuration}ms`);
      console.log(`🔧 Agents Used: ${result.metadata.agentsUsed.join(', ')}`);

      // Display phase results
      result.phases.forEach((phase, index) => {
        console.log(`\n📋 Phase ${index + 1}: ${phase.phase.toUpperCase()}`);
        console.log(`   ✅ Success: ${phase.success}`);
        console.log(`   ⏱️  Duration: ${phase.metadata.duration}ms`);
        console.log(`   🎯 Confidence: ${phase.metadata.confidence || 'N/A'}`);
        
        if (phase.warnings && phase.warnings.length > 0) {
          console.log(`   ⚠️  Warnings: ${phase.warnings.length}`);
          phase.warnings.forEach(warning => console.log(`      - ${warning}`));
        }

        // Show sample output for each phase
        console.log(`   📤 Output Sample:`, JSON.stringify(phase.data, null, 2).substring(0, 200) + '...');
      });

      // Show data flow trace
      console.log('\n📊 Data Flow Trace:');
      result.metadata.dataFlowTrace.forEach(trace => {
        console.log(`   ${trace.phase}: ${trace.inputSize} → ${trace.outputSize} bytes`);
      });

    } else {
      console.error('❌ Pipeline execution failed');
      result.errors.forEach(error => {
        console.error(`   Error in ${error.phase}: ${error.message}`);
      });
    }

    return result;

  } catch (error) {
    console.error('💥 Pipeline execution error:', error);
    throw error;
  }
}

/**
 * Example: Individual Phase Execution
 */
export async function runIndividualPhaseExample() {
  console.log('\n🔧 Individual Phase Execution Example');

  const pipeline = new AEFrameworkPipeline({
    projectId: 'phase-test-001',
    domain: 'e-commerce'
  });

  // Register only Intent Agent for this example
  pipeline.registerAgent('intent', new IntentAgentAdapter());

  const input: IntentInput = {
    sources: [{
      type: 'text',
      content: 'Build an e-commerce platform with shopping cart and payment processing'
    }],
    context: {
      domain: 'e-commerce',
      existingSystem: false
    }
  };

  try {
    // Execute single phase
    const result = await pipeline.executePhase('intent', input, {
      projectId: 'phase-test-001',
      domain: 'e-commerce'
    });

    console.log('Phase Result:', {
      success: result.success,
      phase: result.phase,
      duration: result.metadata.duration,
      outputKeys: Object.keys(result.data)
    });

    return result;

  } catch (error) {
    console.error('Phase execution error:', error);
    throw error;
  }
}

/**
 * Example: Pipeline Capabilities Inspection
 */
export function inspectPipelineCapabilities() {
  console.log('\n🔍 Pipeline Capabilities Inspection');

  const pipeline = new AEFrameworkPipeline({
    projectId: 'capabilities-test',
    domain: 'general'
  });

  // Register all agents
  pipeline.registerAgent('intent', new IntentAgentAdapter());
  pipeline.registerAgent('requirements', new RequirementsAgentAdapter());
  pipeline.registerAgent('user-stories', new UserStoriesAgentAdapter());
  pipeline.registerAgent('validation', new ValidationAgentAdapter());
  pipeline.registerAgent('domain-modeling', new DomainModelingAgentAdapter());
  pipeline.registerAgent('ui-ux-generation', new UIUXAgentAdapter());

  // Get capabilities for each phase
  const capabilities = pipeline.getPipelineCapabilities();

  Object.entries(capabilities).forEach(([phase, capability]) => {
    console.log(`\n📋 ${phase.toUpperCase()} Phase Capabilities:`);
    console.log(`   🔧 Supported Inputs: ${capability.supportedInputTypes.join(', ')}`);
    console.log(`   📤 Output Schema: ${capability.outputSchema}`);
    console.log(`   ✅ Required Context: ${capability.requiredContext.join(', ')}`);
    console.log(`   🔄 Optional Context: ${capability.optionalContext.join(', ')}`);
    console.log(`   ⏱️  Est. Processing Time: ${capability.estimatedProcessingTime || 'N/A'}ms`);
    if (capability.maxInputSize) {
      console.log(`   📏 Max Input Size: ${capability.maxInputSize} bytes`);
    }
  });
}

/**
 * Example: Benchmark Integration
 * Shows how to integrate with req2run-benchmark using standardized pipeline
 */
export async function benchmarkIntegrationExample() {
  console.log('\n🏆 Benchmark Integration Example');

  // This would integrate with the existing BenchmarkRunner
  const pipeline = new AEFrameworkPipeline({
    projectId: 'benchmark-integration',
    domain: 'cli-tool'
  });

  // Register all agents
  pipeline.registerAgent('intent', new IntentAgentAdapter());
  pipeline.registerAgent('requirements', new RequirementsAgentAdapter());
  pipeline.registerAgent('user-stories', new UserStoriesAgentAdapter());
  pipeline.registerAgent('validation', new ValidationAgentAdapter());
  pipeline.registerAgent('domain-modeling', new DomainModelingAgentAdapter());
  pipeline.registerAgent('ui-ux-generation', new UIUXAgentAdapter());

  // Simulate benchmark problem input
  const benchmarkInput: IntentInput = {
    sources: [{
      type: 'specification',
      content: `
        CLI-001: File Processing Tool
        
        Functional Requirements:
        - Convert between CSV, JSON, and TXT formats
        - Support batch processing of multiple files
        - Provide detailed error reporting
        - Include progress indicators for long operations
        
        Non-Functional Requirements:
        - Processing time < 5 seconds for files up to 100MB
        - Memory usage < 512MB for large file operations
        - Cross-platform compatibility (Windows, macOS, Linux)
      `,
      metadata: {
        problemId: 'CLI-001',
        category: 'CLI Tools',
        difficulty: 'intermediate'
      }
    }],
    context: {
      domain: 'command-line-tools',
      constraints: [
        {
          type: 'technical',
          description: 'Must use only standard libraries',
          impact: 'high',
          source: 'benchmark_constraints'
        }
      ]
    }
  };

  try {
    const result = await pipeline.executePipeline(benchmarkInput);
    
    // This result could be returned to BenchmarkRunner for evaluation
    console.log('Benchmark Pipeline Result:', {
      success: result.success,
      totalDuration: result.totalDuration,
      phasesCompleted: result.phases.length,
      errorCount: result.errors.length
    });

    return result;

  } catch (error) {
    console.error('Benchmark integration error:', error);
    throw error;
  }
}

// Export for usage in tests or other modules
export {
  runCompleteAEFrameworkPipeline as default,
  runIndividualPhaseExample,
  inspectPipelineCapabilities,
  benchmarkIntegrationExample
};

// Self-executing example if run directly
if (import.meta.url === `file://${process.argv[1]}`) {
  console.log('🎯 Running AE Framework Pipeline Integration Examples\n');
  
  Promise.resolve()
    .then(() => inspectPipelineCapabilities())
    .then(() => runIndividualPhaseExample())
    .then(() => runCompleteAEFrameworkPipeline())
    .then(() => benchmarkIntegrationExample())
    .then(() => console.log('\n✅ All examples completed successfully!'))
    .catch(error => {
      console.error('\n❌ Example execution failed:', error);
      process.exit(1);
    });
}