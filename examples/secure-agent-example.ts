/**
 * Example: How to implement secure validation in concrete agents
 * Phase 1.2 Security Pattern Demonstration
 */

import { BaseAgent, AgentOutput } from '../src/agents/base-agent';
import { ValidationResult } from '../src/cli/types';
import { PhaseType } from '../src/utils/phase-state-manager';

/**
 * Example: Intent Agent with secure validation
 */
class SecureIntentAgent extends BaseAgent {
  constructor() {
    super('intent' as PhaseType);
  }

  /**
   * Override the default validation with custom requirements validation
   */
  protected async validate(output: AgentOutput): Promise<ValidationResult> {
    const details: { check: string; passed: boolean; message?: string }[] = [];
    let allPassed = true;

    // Check 1: Content should not be empty
    const hasContent = output.content && output.content.trim().length > 0;
    details.push({
      check: 'content_not_empty',
      passed: hasContent,
      message: hasContent ? 'Content is present' : 'Content cannot be empty'
    });
    if (!hasContent) allPassed = false;

    // Check 2: Should have at least one artifact
    const hasArtifacts = output.artifacts.length > 0;
    details.push({
      check: 'has_artifacts',
      passed: hasArtifacts,
      message: hasArtifacts ? `Has ${output.artifacts.length} artifacts` : 'At least one artifact is required'
    });
    if (!hasArtifacts) allPassed = false;

    // Check 3: Quality score should be reasonable (if provided)
    if (output.quality) {
      const goodQuality = output.quality.score >= 70;
      details.push({
        check: 'quality_threshold',
        passed: goodQuality,
        message: goodQuality ? `Quality score: ${output.quality.score}` : `Quality score too low: ${output.quality.score}`
      });
      if (!goodQuality) allPassed = false;
    }

    return {
      success: allPassed,
      message: allPassed ? 'All validation checks passed' : 'Some validation checks failed',
      details
    };
  }

  /**
   * Main processing method that uses secure validation
   */
  async processRequirements(userInput: string): Promise<{ output: AgentOutput; validation: ValidationResult }> {
    // Check if we can proceed
    const canProceed = await this.canProceed();
    if (!canProceed.canProceed) {
      throw new Error(`Cannot proceed: ${canProceed.reason}`);
    }

    // Initialize phase if needed
    await this.initializePhase();

    // Generate output (this is where the actual AI processing would happen)
    const output: AgentOutput = {
      type: 'requirements',
      content: `Requirements analysis for: ${userInput}`,
      artifacts: ['requirements.md', 'user-stories.md'],
      metadata: {
        timestamp: new Date().toISOString(),
        inputLength: userInput.length
      },
      quality: {
        score: 85,
        metrics: {
          completeness: 90,
          clarity: 80
        }
      }
    };

    // Use secure validation - this will never crash the system
    const validation = await this.validateOutput(output);

    if (validation.success) {
      await this.completePhase(output.artifacts);
    }

    return { output, validation };
  }
}

/**
 * Example: Agent with minimal validation (falls back to safe default)
 */
class MinimalAgent extends BaseAgent {
  constructor() {
    super('code' as PhaseType);
  }

  // This agent doesn't override validate() - it will use the safe default

  async generateCode(specification: string): Promise<{ output: AgentOutput; validation: ValidationResult }> {
    const output: AgentOutput = {
      type: 'code',
      content: `Generated code based on: ${specification}`,
      artifacts: ['main.ts', 'main.test.ts']
    };

    // Safe validation will always pass with default implementation
    const validation = await this.validateOutput(output);

    return { output, validation };
  }
}

/**
 * Example usage and testing
 */
async function demonstrateSecureValidation() {
  console.log('🔒 BaseAgent Security Pattern Demonstration\n');

  // Test secure validation with custom implementation
  const secureAgent = new SecureIntentAgent();
  
  try {
    const result1 = await secureAgent.processRequirements('Create a user management system');
    console.log('✅ Secure Agent Result:');
    console.log(`   Success: ${result1.validation.success}`);
    console.log(`   Message: ${result1.validation.message}`);
    console.log(`   Checks: ${result1.validation.details.length}`);
    
  } catch (error) {
    console.log('❌ Secure Agent Error:', error);
  }

  // Test with minimal agent (safe default)
  const minimalAgent = new MinimalAgent();
  
  try {
    const result2 = await minimalAgent.generateCode('User authentication module');
    console.log('\n✅ Minimal Agent Result (safe default):');
    console.log(`   Success: ${result2.validation.success}`);
    console.log(`   Message: ${result2.validation.message}`);
    console.log(`   Fallback: Uses safe default validation`);
    
  } catch (error) {
    console.log('❌ Minimal Agent Error:', error);
  }

  console.log('\n🎯 Key Security Benefits:');
  console.log('   1. Default validation never crashes the system');
  console.log('   2. Custom validation exceptions are caught safely');
  console.log('   3. Logging failures fall back to console output');
  console.log('   4. All agents have consistent validation interface');
}

// Export for use in other examples
export { SecureIntentAgent, MinimalAgent, demonstrateSecureValidation };