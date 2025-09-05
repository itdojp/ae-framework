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
