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

