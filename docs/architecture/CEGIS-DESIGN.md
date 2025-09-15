# CEGIS (Counterexample-Guided Inductive Synthesis) Design Document

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

CEGIS は反例誘導帰納合成により、仕様逸脱を検出した際の自動修復（セルフリペア）を実現します。設計の要点:
- 反例に基づく学習とテンプレート駆動の修復計画
- 形式検証（TLA+/Alloy）と実行時モニタの橋渡し
- ランタイム適合性（Phase 2.2）との連携による自動回復フロー

詳細は下の英語セクションのアーキテクチャ/コンポーネント図を参照してください。

## 日本語（詳細）

### 1. 概要
CEGIS（Counterexample-Guided Inductive Synthesis）は、検証や実行時の反例から修復知識を獲得し、コード/構成を自動修復する設計です。

### 1.1 目的
- 自動修復: 仕様逸脱時に自己修復
- 適応生成: 反例に基づくコード/設定の漸進的洗練
- 継続学習: 反例データベースを用いた知識強化
- フォーマル連携: 仕様検査とランタイムの橋渡し

### 2. コンポーネント
- Synthesizer: コード生成/テンプレ選択/修復計画
- Verifier: 形式検査/ランタイム監視/不変量検証
- Learner: 反例パターン拡張/規則推論/ヒューリスティク更新
- Counterexample DB / Knowledge Base / Repair Executor

### 2.1 処理フロー（例）
1) 逸脱検出（verify/ランタイム）→ 反例保存
2) 反例から修復候補を合成（テンプレ+文脈）
3) 検証（TLA+/Alloy or runtime stubs）で安全性確認
4) 候補を適用（dry-run→実適用）し再検証

### 2.2 AE-Framework への組込み
- Formal/Runtime の双方から反例導入
- OpenAPI コード生成で runtime contracts を注入し、修復評価の足場を用意
- PR サマリへ反例→修復の要約を出力、ゲートはラベルで opt-in

## 1. Overview

This document outlines the design for implementing CEGIS (Counterexample-Guided Inductive Synthesis) in the AE-Framework. CEGIS enables counterexample-driven self-repair, providing automated system recovery and adaptation capabilities for Phase 7-8 implementation.

### 1.1 Purpose

CEGIS provides:
- **Automated Error Recovery**: Self-repair when system behavior deviates from specifications
- **Adaptive Code Generation**: Dynamic refinement of generated code based on runtime feedback
- **Continuous Learning**: System improvement through counterexample analysis
- **Formal Verification Integration**: Bridge between formal specifications and runtime behavior

### 1.2 Key Concepts

- **Synthesis**: Automated generation of correct-by-construction implementations
- **Counterexample**: Evidence of specification violations discovered during verification or runtime
- **Inductive Reasoning**: Learning from specific counterexamples to generalize solutions
- **Self-Repair**: Automatic correction of system behavior without manual intervention

## 2. Architecture

### 2.1 System Components

```
┌─────────────────────────────────────────────────────────────┐
│                    CEGIS Engine                            │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐ │
│  │  Synthesizer    │  │  Verifier       │  │  Learner        │ │
│  │                 │  │                 │  │                 │ │
│  │ • Code Gen      │  │ • Formal Check  │  │ • Pattern Ext   │ │
│  │ • Template Sel  │  │ • Runtime Mon   │  │ • Rule Infer    │ │
│  │ • Repair Plans  │  │ • Invariant Val │  │ • Heuristic Up  │ │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘ │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐ │
│  │ Counterexample  │  │  Knowledge      │  │  Repair         │ │
│  │   Database      │  │    Base         │  │  Executor       │ │
│  │                 │  │                 │  │                 │ │
│  │ • Error Traces  │  │ • Repair Rules  │  │ • Code Apply    │ │
│  │ • Context Info  │  │ • Template Lib  │  │ • State Rollb   │ │
│  │ • Fix History   │  │ • Pattern Cache │  │ • Validation    │ │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘ │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 Integration with AE-Framework

```
┌─────────────────────────────────────────────────────────────┐
│                    AE-Framework Integration                 │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  AE-IR Spec ──→ Synthesizer ──→ Generated Code              │
│      │              │                   │                   │
│      │              │                   ↓                   │
│      │              │           Runtime Monitor             │
│      │              │                   │                   │
│      │              │           Counterexample              │
│      │              │                   │                   │
│      │              ↓                   │                   │
│      └─────→ Verifier ←──────────────────┘                   │
│                     │                                       │
│                     ↓                                       │
│               Learner & Repair                              │
│                     │                                       │
│                     ↓                                       │
│              Updated AE-IR/Templates                        │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## 3. Core Components

### 3.1 CEGIS Synthesizer

**Purpose**: Generate code implementations from AE-IR specifications with built-in repair capabilities.

**Key Features**:
- Template-based code generation with repair markers
- Multiple synthesis strategies (reactive, proactive, hybrid)
- Integration with existing deterministic code generator
- Support for incremental refinement

**Interface**:
```typescript
interface CEGISSynthesizer {
  synthesize(spec: AEIR, constraints: SynthesisConstraints): Promise<SynthesisResult>;
  repair(counterexample: Counterexample, context: RepairContext): Promise<RepairPlan>;
  refine(plan: RepairPlan, feedback: ValidationFeedback): Promise<RefinedSolution>;
}

interface SynthesisResult {
  generatedCode: GeneratedFile[];
  repairPoints: RepairPoint[];
  confidence: number;
  verificationRequirements: VerificationSpec[];
}
```

### 3.2 CEGIS Verifier

**Purpose**: Detect specification violations and generate meaningful counterexamples.

**Verification Methods**:
- **Static Analysis**: Type checking, contract verification, invariant validation
- **Dynamic Monitoring**: Runtime contract checking, performance thresholds
- **Formal Methods**: Model checking, theorem proving integration
- **Property-Based Testing**: Automated test generation and execution

**Interface**:
```typescript
interface CEGISVerifier {
  verify(code: GeneratedCode, spec: AEIR): Promise<VerificationResult>;
  monitor(runtime: RuntimeContext): Promise<MonitoringResult>;
  generateCounterexample(violation: SpecViolation): Promise<Counterexample>;
}

interface Counterexample {
  id: string;
  violationType: ViolationType;
  context: ExecutionContext;
  trace: ExecutionTrace;
  expectedBehavior: SpecifiedBehavior;
  actualBehavior: ObservedBehavior;
  severity: 'critical' | 'high' | 'medium' | 'low';
  reproducible: boolean;
}
```

### 3.3 CEGIS Learner

**Purpose**: Extract patterns from counterexamples and build a knowledge base for improved synthesis.

**Learning Strategies**:
- **Pattern Recognition**: Identify common failure modes and successful repair patterns
- **Rule Inference**: Generate repair rules from successful counterexample resolutions
- **Template Evolution**: Improve code generation templates based on feedback
- **Heuristic Development**: Build domain-specific repair strategies

**Interface**:
```typescript
interface CEGISLearner {
  learn(counterexample: Counterexample, repair: SuccessfulRepair): Promise<LearningResult>;
  inferRule(pattern: FailurePattern): Promise<RepairRule>;
  evolveTemplate(template: CodeTemplate, feedback: RepairFeedback[]): Promise<ImprovedTemplate>;
  buildHeuristic(domain: DomainContext, examples: CounterexampleSet): Promise<RepairHeuristic>;
}

interface RepairRule {
  id: string;
  pattern: FailurePattern;
  condition: LogicalCondition;
  action: RepairAction;
  confidence: number;
  applicabilityScope: string[];
}
```

## 4. Implementation Strategy

### 4.1 Phase 7: Foundation (Runtime Monitoring)

**Objectives**:
- Implement basic runtime monitoring infrastructure
- Build counterexample detection and collection system
- Create initial repair rule database
- Integrate with existing quality gates

**Deliverables**:
- `CEGISMonitor` class for runtime contract checking
- `CounterexampleCollector` for violation detection
- `RepairRuleDatabase` for pattern storage
- Integration with GuardRunner and quality policy system

**Implementation Timeline**: 2-3 sprints

### 4.2 Phase 8: Advanced Synthesis (Self-Repair)

**Objectives**:
- Implement automated repair synthesis
- Build adaptive code generation capabilities
- Create learning and evolution mechanisms
- Provide comprehensive CEGIS pipeline

**Deliverables**:
- Full CEGIS engine implementation
- Advanced repair strategies
- Template evolution system
- Performance optimization and scaling

**Implementation Timeline**: 4-6 sprints

### 4.3 Integration Points

#### 4.3.1 AE-IR Specification Enhancement

Extend AE-IR format to include repair annotations:

```json
{
  "version": "1.1.0",
  "repair": {
    "enabled": true,
    "strategies": ["reactive", "proactive"],
    "repairPoints": [
      {
        "entity": "Order",
        "field": "totalAmount",
        "invariant": "totalAmount >= 0",
        "repairAction": "recalculate_from_items"
      }
    ]
  }
}
```

#### 4.3.2 Quality Policy Integration

Enhance quality.json with CEGIS configuration:

```json
{
  "cegis": {
    "description": "Counterexample-Guided Inductive Synthesis",
    "enforcement": "strict",
    "enabledFromPhase": "phase-7",
    "thresholds": {
      "repairSuccessRate": 0.85,
      "learningEfficiency": 0.70,
      "synthesisAccuracy": 0.90
    },
    "strategies": {
      "reactive": true,
      "proactive": false,
      "hybrid": true
    }
  }
}
```

#### 4.3.3 CLI Enhancement

Add CEGIS commands to the CLI:

```bash
# Monitor and collect counterexamples
pnpm ae-framework cegis monitor --target=production --duration=24h

# Synthesize repairs for collected counterexamples
pnpm ae-framework cegis repair --counterexample-id=ce_001 --strategy=reactive

# Learn from repair history
pnpm ae-framework cegis learn --pattern=validation_failures --domain=orders

# Status and metrics
pnpm ae-framework cegis status --detailed
```

## 5. Technical Implementation

### 5.1 Core CEGIS Engine

```typescript
/**
 * Core CEGIS Engine Implementation
 * Integrates synthesis, verification, and learning components
 */
export class CEGISEngine {
  private synthesizer: CEGISSynthesizer;
  private verifier: CEGISVerifier;
  private learner: CEGISLearner;
  private executor: RepairExecutor;
  private database: CounterexampleDatabase;

  constructor(
    private config: CEGISConfig,
    private qualityPolicy: QualityPolicy,
    private aeir: AEIR
  ) {
    this.synthesizer = new CEGISSynthesizer(config.synthesis);
    this.verifier = new CEGISVerifier(config.verification);
    this.learner = new CEGISLearner(config.learning);
    this.executor = new RepairExecutor(config.execution);
    this.database = new CounterexampleDatabase(config.storage);
  }

  /**
   * Main CEGIS loop
   */
  async runCEGISLoop(initialSpec: AEIR): Promise<CEGISResult> {
    let currentSpec = initialSpec;
    let iteration = 0;
    const maxIterations = this.config.maxIterations || 10;

    while (iteration < maxIterations) {
      // Synthesis phase
      const synthesis = await this.synthesizer.synthesize(
        currentSpec,
        this.getSynthesisConstraints()
      );

      // Verification phase
      const verification = await this.verifier.verify(
        synthesis.generatedCode,
        currentSpec
      );

      if (verification.isValid) {
        return {
          success: true,
          finalSolution: synthesis,
          iterations: iteration + 1,
          repairs: [],
        };
      }

      // Learning phase
      const counterexamples = verification.counterexamples;
      for (const ce of counterexamples) {
        await this.database.store(ce);
        
        // Generate repair
        const repair = await this.synthesizer.repair(
          ce,
          this.getRepairContext(ce)
        );

        // Execute repair
        const repairResult = await this.executor.execute(repair);

        if (repairResult.success) {
          // Learn from successful repair
          await this.learner.learn(ce, repairResult.repair);
          
          // Update specification if needed
          currentSpec = await this.updateSpecification(
            currentSpec,
            repairResult.refinements
          );
        }
      }

      iteration++;
    }

    throw new Error(`CEGIS failed to converge after ${maxIterations} iterations`);
  }

  /**
   * Reactive repair for runtime violations
   */
  async reactiveRepair(violation: RuntimeViolation): Promise<RepairResult> {
    const counterexample = await this.verifier.generateCounterexample(violation);
    
    // Check for known repair patterns
    const knownPattern = await this.learner.findMatchingPattern(counterexample);
    if (knownPattern) {
      const repair = await this.synthesizer.applyKnownRepair(
        knownPattern,
        counterexample
      );
      return await this.executor.execute(repair);
    }

    // Generate new repair
    const repair = await this.synthesizer.repair(
      counterexample,
      this.getRepairContext(counterexample)
    );

    const result = await this.executor.execute(repair);
    
    if (result.success) {
      // Learn from new successful repair
      await this.learner.learn(counterexample, result.repair);
    }

    return result;
  }

  private getSynthesisConstraints(): SynthesisConstraints {
    return {
      qualityThresholds: this.qualityPolicy.getThresholds('cegis'),
      performanceRequirements: this.config.performance,
      securityConstraints: this.config.security,
      repairability: true,
    };
  }

  private getRepairContext(counterexample: Counterexample): RepairContext {
    return {
      specification: this.aeir,
      qualityPolicy: this.qualityPolicy,
      executionEnvironment: this.config.environment,
      constraintViolations: counterexample.violations,
      availableStrategies: this.config.repairStrategies,
    };
  }
}
```

### 5.2 Counterexample Database Schema

```typescript
interface CounterexampleSchema {
  // Primary identification
  id: string;
  timestamp: Date;
  
  // Context information
  specificationVersion: string;
  codeVersion: string;
  executionEnvironment: EnvironmentInfo;
  
  // Violation details
  violationType: ViolationType;
  severity: SeverityLevel;
  affectedEntities: string[];
  
  // Execution trace
  stackTrace: StackFrame[];
  inputParameters: Record<string, any>;
  expectedOutput: any;
  actualOutput: any;
  
  // Repair information
  repairAttempts: RepairAttempt[];
  successfulRepair?: SuccessfulRepair;
  
  // Learning metadata
  patterns: string[];
  similarCounterexamples: string[];
  generalizations: string[];
}

interface RepairAttempt {
  strategy: string;
  timestamp: Date;
  success: boolean;
  changes: CodeChange[];
  validationResults: ValidationResult[];
}
```

## 6. Quality Assurance

### 6.1 Testing Strategy

**Unit Testing**:
- Individual component testing for synthesizer, verifier, learner
- Mock-based testing for complex interactions
- Property-based testing for CEGIS algorithms

**Integration Testing**:
- End-to-end CEGIS loop validation
- Cross-component communication testing
- Performance and scalability testing

**Validation Testing**:
- Repair effectiveness measurement
- Learning accuracy validation
- Convergence time analysis

### 6.2 Metrics and Monitoring

**Key Performance Indicators**:
- Repair success rate (target: ≥85%)
- Learning efficiency (pattern recognition accuracy)
- Synthesis quality (generated code correctness)
- Convergence time (CEGIS loop iterations)

**Monitoring Implementation**:
```typescript
interface CEGISMetrics {
  repairSuccessRate: number;
  averageRepairTime: number;
  learningAccuracy: number;
  synthesisQuality: number;
  counterexamplesCollected: number;
  patternsLearned: number;
  convergenceIterations: number;
}
```

## 7. Security and Privacy

### 7.1 Security Considerations

- **Code Integrity**: Ensure repairs don't introduce security vulnerabilities
- **Access Control**: Restrict CEGIS operations to authorized users/systems
- **Audit Trail**: Maintain complete logs of all repair operations
- **Rollback Capability**: Provide safe rollback mechanisms for failed repairs

### 7.2 Privacy Protection

- **Data Sanitization**: Remove sensitive information from counterexamples
- **Differential Privacy**: Protect individual user data in learning processes
- **Secure Storage**: Encrypt counterexample database and knowledge base

## 8. Deployment and Operations

### 8.1 Deployment Architecture

```
┌─────────────────────────────────────────────┐
│                Production                   │
├─────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐           │
│  │   App       │  │ CEGIS       │           │
│  │ Runtime     │  │ Monitor     │           │
│  │             │  │             │           │
│  └─────────────┘  └─────────────┘           │
├─────────────────────────────────────────────┤
│                Development                  │
├─────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐           │
│  │ CEGIS       │  │ Knowledge   │           │
│  │ Engine      │  │ Base        │           │
│  │             │  │             │           │
│  └─────────────┘  └─────────────┘           │
└─────────────────────────────────────────────┘
```

### 8.2 Operational Procedures

**Monitoring**:
- Real-time violation detection
- Performance metric tracking
- Alert escalation procedures

**Maintenance**:
- Knowledge base updates
- Pattern validation and cleanup
- Performance optimization

**Incident Response**:
- Automated repair attempts
- Escalation to human operators
- Root cause analysis and prevention

## 9. Future Enhancements

### 9.1 Advanced Features

- **Multi-Modal Learning**: Incorporate natural language feedback
- **Distributed CEGIS**: Scale across multiple systems and environments
- **Predictive Repair**: Anticipate violations before they occur
- **Domain-Specific Specialization**: Tailor CEGIS for specific application domains

### 9.2 Research Integration

- **Formal Methods**: Deeper integration with theorem provers
- **Machine Learning**: Advanced pattern recognition and synthesis
- **Human-in-the-Loop**: Incorporate expert knowledge and feedback
- **Cross-System Learning**: Share knowledge across different deployments

## 10. Conclusion

The CEGIS design provides a comprehensive framework for implementing counterexample-driven self-repair in the AE-Framework. This design enables:

1. **Automated Recovery**: System-level self-healing capabilities
2. **Continuous Improvement**: Learning from operational experience
3. **Specification Evolution**: Dynamic refinement of system requirements
4. **Quality Assurance**: Formal verification integrated with practical deployment

The phased implementation approach ensures manageable development complexity while providing incremental value. Integration with existing AE-Framework components (quality policies, CLI, monitoring) ensures seamless adoption and consistent user experience.

This CEGIS implementation will position the AE-Framework as a leader in self-adaptive software systems, providing robust, intelligent, and continuously improving software solutions.
