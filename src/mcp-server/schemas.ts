import { z } from 'zod';

export const VerificationTypeEnum = z.enum([
  'tests',
  'coverage',
  'linting',
  'typechecking',
  'security',
  'performance',
  'accessibility',
  'contracts',
  'specifications',
  'mutations',
]);

export const FullVerificationArgsSchema = z.object({
  projectPath: z.string().min(1, 'projectPath is required'),
  verificationTypes: z.array(VerificationTypeEnum).min(1, 'at least one verification type required'),
  strictMode: z.boolean().optional().default(false),
});
export type FullVerificationArgs = z.infer<typeof FullVerificationArgsSchema>;

export const TestTypeEnum = z.enum(['unit', 'integration', 'e2e', 'property', 'contract']);
export const RunTestsArgsSchema = z.object({
  projectPath: z.string().min(1),
  testTypes: z.array(TestTypeEnum).optional().default(['unit', 'integration', 'e2e']),
});
export type RunTestsArgs = z.infer<typeof RunTestsArgsSchema>;

export const CoverageArgsSchema = z.object({
  projectPath: z.string().min(1),
  threshold: z.number().optional().default(80),
});
export type CoverageArgs = z.infer<typeof CoverageArgsSchema>;

export const LintingArgsSchema = z.object({
  projectPath: z.string().min(1),
  fix: z.boolean().optional().default(false),
});
export type LintingArgs = z.infer<typeof LintingArgsSchema>;

export const TypeCheckingArgsSchema = z.object({
  projectPath: z.string().min(1),
  strict: z.boolean().optional().default(true),
});
export type TypeCheckingArgs = z.infer<typeof TypeCheckingArgsSchema>;

export const SecurityScanArgsSchema = z.object({
  projectPath: z.string().min(1),
  includeDevDeps: z.boolean().optional().default(true),
});
export type SecurityScanArgs = z.infer<typeof SecurityScanArgsSchema>;

export function parseOrThrow<T extends z.ZodTypeAny>(schema: T, input: unknown): z.infer<T> {
  const res = schema.safeParse(input);
  if (!res.success) {
    const msg = res.error.issues.map(i => `${i.path.join('.') || '(root)'}: ${i.message}`).join('; ');
    throw new Error(`Invalid arguments: ${msg}`);
  }
  return res.data;
}

// ---------- Test Generation MCP Schemas ----------
export const TestFrameworkEnum = z.enum(['vitest', 'jest', 'mocha']);

export const GenerateFromRequirementsArgsSchema = z.object({
  feature: z.string().min(1),
  requirements: z.array(z.string()).optional().default([]),
  testFramework: TestFrameworkEnum.optional().default('vitest'),
});
export type GenerateFromRequirementsArgs = z.infer<typeof GenerateFromRequirementsArgsSchema>;

export const GenerateFromCodeArgsSchema = z.object({
  codeFile: z.string().min(1),
});
export type GenerateFromCodeArgs = z.infer<typeof GenerateFromCodeArgsSchema>;

const InputParamSchema = z.object({
  name: z.string().min(1),
  type: z.string().min(1),
  constraints: z.array(z.string()).optional().default([]),
});

export const PropertyTestsArgsSchema = z.object({
  functionName: z.string().min(1),
  inputs: z.array(InputParamSchema).min(1),
  outputs: z
    .object({ type: z.string().min(1) })
    .optional()
    .default({ type: 'any' }),
  invariants: z.array(z.string()).min(1),
});
export type PropertyTestsArgs = z.infer<typeof PropertyTestsArgsSchema>;

export const BDDArgsSchema = z.object({
  title: z.string().min(1),
  asA: z.string().min(1),
  iWant: z.string().min(1),
  soThat: z.string().min(1),
  acceptanceCriteria: z.array(z.string()).optional().default([]),
});
export type BDDArgs = z.infer<typeof BDDArgsSchema>;

const AnyObj = z.object({}).passthrough();

export const PlanIntegrationArgsSchema = z.object({
  services: z.array(z.union([AnyObj, z.string()])).min(1),
  dataFlow: z.array(AnyObj).optional().default([]),
});
export type PlanIntegrationArgs = z.infer<typeof PlanIntegrationArgsSchema>;

export const SecurityTestsArgsSchema = z.object({
  endpoint: z.object({
    method: z.string().min(1),
    path: z.string().min(1),
  }),
});
export type SecurityTestsArgs = z.infer<typeof SecurityTestsArgsSchema>;

export const PerformanceSLAInput = z.object({
  responseTime: z.number().optional(),
  throughput: z.number().optional(),
  concurrentUsers: z.number().optional(),
  availability: z.number().optional(),
});
export const DesignPerformanceArgsSchema = z.object({
  sla: PerformanceSLAInput,
});
export type DesignPerformanceArgs = z.infer<typeof DesignPerformanceArgsSchema>;

export const AnalyzeCoverageArgsSchema = z.object({
  projectPath: z.string().optional().default('.'),
});
export type AnalyzeCoverageArgs = z.infer<typeof AnalyzeCoverageArgsSchema>;

// ---------- Container MCP Schemas ----------
export const LanguageEnum = z.enum(['rust', 'elixir', 'multi']);

export const RunContainerVerificationArgsSchema = z.object({
  projectPath: z.string().min(1),
  language: LanguageEnum,
  tools: z.array(z.string()).min(1),
  jobName: z.string().optional(),
  timeout: z.number().optional(),
  buildImages: z.boolean().optional().default(false),
  environment: z.record(z.string()).optional().default({}),
});
export type RunContainerVerificationArgs = z.infer<typeof RunContainerVerificationArgsSchema>;

export const BuildVerificationImageArgsSchema = z.object({
  language: LanguageEnum,
  tools: z.array(z.string()).min(1),
  baseImage: z.string().optional(),
  tag: z.string().optional(),
  push: z.boolean().optional().default(false),
  buildArgs: z.record(z.string()).optional().default({}),
});
export type BuildVerificationImageArgs = z.infer<typeof BuildVerificationImageArgsSchema>;

export const GetJobStatusArgsSchema = z.object({ jobId: z.string().min(1) });
export type GetJobStatusArgs = z.infer<typeof GetJobStatusArgsSchema>;

export const ListJobsArgsSchema = z.object({
  status: z.enum(['pending', 'running', 'completed', 'failed']).optional(),
  language: LanguageEnum.optional(),
});
export type ListJobsArgs = z.infer<typeof ListJobsArgsSchema>;

export const CancelJobArgsSchema = z.object({ jobId: z.string().min(1) });
export type CancelJobArgs = z.infer<typeof CancelJobArgsSchema>;

export const CleanupArgsSchema = z.object({
  maxAge: z.number().optional().default(3600),
  keepCompleted: z.number().optional().default(10),
  force: z.boolean().optional().default(false),
});
export type CleanupArgs = z.infer<typeof CleanupArgsSchema>;

// ---------- TDD MCP Schemas ----------
export const AnalyzeTDDArgsSchema = z.object({
  path: z.string().optional().default(process.cwd()),
  phase: z.string().optional(),
});
export type AnalyzeTDDArgs = z.infer<typeof AnalyzeTDDArgsSchema>;

export const GuideTDDArgsSchema = z.object({
  feature: z.string().min(1),
  currentStep: z.string().optional(),
});
export type GuideTDDArgs = z.infer<typeof GuideTDDArgsSchema>;

export const ValidateTestFirstArgsSchema = z.object({
  sourceFiles: z.array(z.string()).optional().default([]),
});
export type ValidateTestFirstArgs = z.infer<typeof ValidateTestFirstArgsSchema>;

export const RedGreenCycleArgsSchema = z.object({
  testCommand: z.string().optional().default('npm test'),
  expectRed: z.boolean().optional().default(false),
});
export type RedGreenCycleArgs = z.infer<typeof RedGreenCycleArgsSchema>;

export const SuggestTestStructureArgsSchema = z.object({
  codeFile: z.string().min(1),
  framework: z.string().optional().default('vitest'),
});
export type SuggestTestStructureArgs = z.infer<typeof SuggestTestStructureArgsSchema>;

// ---------- Intent MCP Schemas ----------
const RequirementSourceType = z.enum(['text','document','conversation','issue','email','diagram']);
const PriorityEnum = z.enum(['critical','high','medium','low']);
const ImpactEnum = z.enum(['high','medium','low']);
const ConstraintSchema = z.object({
  type: z.enum(['technical','business','regulatory','resource']),
  description: z.string(),
  impact: ImpactEnum,
});
const StakeholderSchema = z.object({
  name: z.string(),
  role: z.string(),
  concerns: z.array(z.string()),
  influenceLevel: ImpactEnum,
});
export const RequirementSourceSchema = z.object({
  type: RequirementSourceType,
  content: z.string(),
  metadata: z.object({
    author: z.string().optional(),
    date: z.string().optional(),
    priority: PriorityEnum.optional(),
    tags: z.array(z.string()).optional(),
    references: z.array(z.string()).optional(),
  }).optional(),
});
export type RequirementSourceInput = z.infer<typeof RequirementSourceSchema>;

export const ProjectContextSchema = z.object({
  domain: z.string().optional(),
  existingSystem: z.boolean().optional(),
  constraints: z.array(ConstraintSchema).optional(),
  stakeholders: z.array(StakeholderSchema).optional(),
});

export const AnalyzeIntentArgsSchema = z.object({
  sources: z.array(RequirementSourceSchema).min(1),
  context: ProjectContextSchema.optional(),
  analysisDepth: z.enum(['basic','detailed','comprehensive']).optional().default('detailed'),
  outputFormat: z.enum(['structured','narrative','both']).optional().default('structured'),
});
export type AnalyzeIntentArgs = z.infer<typeof AnalyzeIntentArgsSchema>;

export const ExtractFromNLArgsSchema = z.object({ text: z.string().min(1) });
export type ExtractFromNLArgs = z.infer<typeof ExtractFromNLArgsSchema>;

export const CreateUserStoriesArgsSchema = z.object({ requirements: z.array(z.any()).min(1) });
export type CreateUserStoriesArgs = z.infer<typeof CreateUserStoriesArgsSchema>;

export const BuildDomainModelArgsSchema = z.object({
  requirements: z.array(z.any()).min(1),
  context: ProjectContextSchema.optional(),
});
export type BuildDomainModelArgs = z.infer<typeof BuildDomainModelArgsSchema>;

export const DetectAmbiguitiesArgsSchema = z.object({ sources: z.array(RequirementSourceSchema).min(1) });
export type DetectAmbiguitiesArgs = z.infer<typeof DetectAmbiguitiesArgsSchema>;

export const ValidateCompletenessArgsSchema = z.object({ requirements: z.array(z.any()).min(1) });
export type ValidateCompletenessArgs = z.infer<typeof ValidateCompletenessArgsSchema>;

export const GenerateSpecTemplatesArgsSchema = z.object({ requirements: z.array(z.any()).min(1) });
export type GenerateSpecTemplatesArgs = z.infer<typeof GenerateSpecTemplatesArgsSchema>;

export const PrioritizeRequirementsArgsSchema = z.object({
  requirements: z.array(z.any()).min(1),
  constraints: z.array(z.any()).min(1),
});
export type PrioritizeRequirementsArgs = z.infer<typeof PrioritizeRequirementsArgsSchema>;

export const GenerateAcceptanceCriteriaArgsSchema = z.object({
  requirement: z.any(),
});
export type GenerateAcceptanceCriteriaArgs = z.infer<typeof GenerateAcceptanceCriteriaArgsSchema>;

export const AnalyzeStakeholderConcernsArgsSchema = z.object({
  stakeholders: z.array(StakeholderSchema).min(1),
  requirements: z.array(z.object({ id: z.string(), description: z.string() })).min(1),
});
export type AnalyzeStakeholderConcernsArgs = z.infer<typeof AnalyzeStakeholderConcernsArgsSchema>;

// ---------- Code Generation MCP Schemas ----------
export const GenerateCodeFromTestsArgsSchema = z.object({
  tests: z.array(z.object({
    path: z.string(),
    content: z.string(),
    type: z.enum(['unit','integration','e2e']),
  })).min(1),
  language: z.enum(['typescript','javascript','python','go','rust','elixir']),
  framework: z.string().optional(),
  architecture: z.object({ pattern: z.enum(['mvc','hexagonal','clean','ddd','microservice']) }).optional(),
});
export type GenerateCodeFromTestsArgs = z.infer<typeof GenerateCodeFromTestsArgsSchema>;

export const GenerateAPIFromOpenAPIArgsSchema = z.object({
  spec: z.string(),
  framework: z.enum(['fastify','express','koa']),
  database: z.enum(['postgres','mongodb','mysql']).optional(),
  includeValidation: z.boolean().optional(),
  includeAuth: z.boolean().optional(),
});
export type GenerateAPIFromOpenAPIArgs = z.infer<typeof GenerateAPIFromOpenAPIArgsSchema>;

export const ValidateCodeAgainstTestsArgsSchema = z.object({
  codeFiles: z.array(z.object({ path: z.string(), content: z.string() })).min(1),
  testFiles: z.array(z.object({ path: z.string(), content: z.string() })).min(1),
});
export type ValidateCodeAgainstTestsArgs = z.infer<typeof ValidateCodeAgainstTestsArgsSchema>;
