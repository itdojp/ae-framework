import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';
import { validateAgenticMetricsSemantics } from '../../scripts/ci/lib/agentic-metrics-contract.mjs';

const schema = JSON.parse(
  readFileSync(resolve('schema/agentic-metrics.schema.json'), 'utf8'),
) as Record<string, unknown>;
const sampleFixture = JSON.parse(
  readFileSync(resolve('fixtures/agentic-metrics/sample.agentic-metrics.json'), 'utf8'),
) as Record<string, unknown>;
const agentPrAssuranceFixture = JSON.parse(
  readFileSync(resolve('fixtures/agentic-metrics/agent-pr-assurance-metrics.example.json'), 'utf8'),
) as Record<string, unknown>;
const collectedAgentPrAssuranceFixture = JSON.parse(
  readFileSync(resolve('fixtures/metrics/agent-pr-assurance/expected.agent-pr-assurance-metrics.json'), 'utf8'),
) as Record<string, unknown>;

function compileSchema() {
  const ajv = new Ajv2020({ allErrors: true, strict: false });
  addFormats(ajv);
  return ajv.compile(schema);
}

function expectSemanticError(
  fixture: Record<string, unknown>,
  expectedPath: string,
  expectedKeyword?: string,
) {
  const validate = compileSchema();

  expect(validate(fixture), JSON.stringify(validate.errors)).toBe(true);

  const errors = validateAgenticMetricsSemantics(fixture);
  expect(errors).not.toEqual([]);
  expect(
    errors.some(
      (entry) => entry.instancePath === expectedPath
        && (expectedKeyword === undefined || entry.keyword === expectedKeyword),
    ),
  ).toBe(true);
}

describe('agentic-metrics contract', () => {
  it('validates existing agentic metrics fixtures with and without report-only PR assurance metrics', () => {
    const validate = compileSchema();

    expect(validate(sampleFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validate(agentPrAssuranceFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validateAgenticMetricsSemantics(sampleFixture)).toEqual([]);
    expect(validateAgenticMetricsSemantics(agentPrAssuranceFixture)).toEqual([]);
  });


  it('rejects required-check classification summary drift in collected PR assurance metrics', () => {
    const invalidFixture = structuredClone(collectedAgentPrAssuranceFixture) as {
      agentPrAssurance: {
        productMetrics: {
          required_checks: {
            summary: { policy_semantic_failure_count: number };
          };
        };
      };
    };

    invalidFixture.agentPrAssurance.productMetrics.required_checks.summary.policy_semantic_failure_count = 1;

    expectSemanticError(
      invalidFixture as unknown as Record<string, unknown>,
      '/agentPrAssurance/productMetrics/required_checks/summary/policy_semantic_failure_count',
      'required_check_summary_mismatch',
    );
  });

  it('accepts not_collected required-check summaries without coercing them to zero', () => {
    const notCollectedFixture = structuredClone(collectedAgentPrAssuranceFixture) as {
      agentPrAssurance: {
        productMetrics: {
          required_checks: {
            source: string;
            required: Array<{ name: string } & Record<string, unknown>>;
            summary: Record<string, unknown>;
          };
          ci_rerun_count: unknown;
          ci_rerun_classification_counts: unknown;
        };
        metrics: {
          agent_regression_signal: Record<string, unknown>;
        };
      };
    };
    const requiredNames = notCollectedFixture.agentPrAssurance.productMetrics.required_checks.required
      .map((entry) => entry.name);
    const collectibleSummaryFields = [
      'success_count',
      'pending_count',
      'current_required_failure_count',
      'policy_semantic_failure_count',
      'operational_failure_count',
      'manual_rerun_required_count',
      'stale_or_superseded_failure_count',
      'stale_cancelled_count',
      'superseded_count',
      'same_head_stale_count',
      'semantic_blocking_failure_count',
      'operational_note_count',
    ];
    notCollectedFixture.agentPrAssurance.productMetrics.required_checks = {
      source: 'not_collected',
      required: requiredNames.map((name) => ({
        name,
        collected: false,
        latest: null,
        classification: 'not_collected',
        review_disposition: 'not_collected',
        attempts: 0,
        stale_or_superseded_failure_count: 0,
        stale_attempts: [],
        stale_cancelled_count: 0,
        superseded_count: 0,
        same_head_stale_count: 0,
      })),
      summary: Object.fromEntries([
        ['required_count', requiredNames.length],
        ['collected_count', 0],
        ...collectibleSummaryFields.map((field) => [field, 'not_collected']),
      ]),
    };
    notCollectedFixture.agentPrAssurance.productMetrics.ci_rerun_count = 'not_collected';
    notCollectedFixture.agentPrAssurance.productMetrics.ci_rerun_classification_counts = 'not_collected';
    notCollectedFixture.agentPrAssurance.metrics.agent_regression_signal = {
      currentFailures: 'not_collected',
      staleOrSupersededFailures: 'not_collected',
      operationalNotes: 'not_collected',
      currentRequiredFailures: 'not_collected',
      policySemanticFailures: 'not_collected',
      manualRerunRequired: 'not_collected',
      classificationSource: 'not_collected',
      regressed: false,
    };

    const validate = compileSchema();
    expect(validate(notCollectedFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validateAgenticMetricsSemantics(notCollectedFixture as unknown as Record<string, unknown>)).toEqual([]);

    const invalidFixture = structuredClone(notCollectedFixture);
    invalidFixture.agentPrAssurance.productMetrics.required_checks.summary.success_count = 0;
    expectSemanticError(
      invalidFixture as unknown as Record<string, unknown>,
      '/agentPrAssurance/productMetrics/required_checks/summary/success_count',
      'required_check_summary_mismatch',
    );
  });

  it('keeps agentPrAssurance report-only', () => {
    const validate = compileSchema();
    const invalidFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: { reportOnly?: boolean };
    };

    invalidFixture.agentPrAssurance.reportOnly = false;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/agentPrAssurance/reportOnly')).toBe(true);
  });

  it('allows n/a lane compliance when no lanes are required', () => {
    const validate = compileSchema();
    const nAComplianceFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: {
        metrics: {
          required_lane_compliance: {
            satisfied: number;
            required: number;
            ratio: number | null;
            missingLanes?: string[];
            notApplicable?: boolean;
          };
        };
      };
    };

    nAComplianceFixture.agentPrAssurance.metrics.required_lane_compliance = {
      satisfied: 0,
      required: 0,
      ratio: null,
      missingLanes: [],
      notApplicable: true,
    };

    expect(validate(nAComplianceFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validateAgenticMetricsSemantics(nAComplianceFixture as unknown as Record<string, unknown>)).toEqual([]);
  });

  it('requires all named report-only agent PR assurance metrics when the extension is present', () => {
    const validate = compileSchema();
    const invalidFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: { metrics: Record<string, unknown> };
    };

    delete invalidFixture.agentPrAssurance.metrics.false_block_rate;

    expect(validate(invalidFixture)).toBe(false);
    expect(validate.errors?.some((entry) => entry.instancePath === '/agentPrAssurance/metrics')).toBe(true);
  });

  it.each([
    {
      name: 'claim_coverage numerator greater than denominator',
      expectedPath: '/agentPrAssurance/metrics/claim_coverage/numerator',
      expectedKeyword: 'metric_count_order',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { claim_coverage: { numerator: number } };
          }
        ).metrics.claim_coverage;
        metric.numerator = 6;
      },
    },
    {
      name: 'claim_coverage ratio mismatch',
      expectedPath: '/agentPrAssurance/metrics/claim_coverage/ratio',
      expectedKeyword: 'metric_ratio_mismatch',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { claim_coverage: { ratio: number } };
          }
        ).metrics.claim_coverage;
        metric.ratio = 0.7;
      },
    },
    {
      name: 'required_lane_compliance satisfied greater than required',
      expectedPath: '/agentPrAssurance/metrics/required_lane_compliance/satisfied',
      expectedKeyword: 'metric_count_order',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { required_lane_compliance: { satisfied: number } };
          }
        ).metrics.required_lane_compliance;
        metric.satisfied = 5;
      },
    },
    {
      name: 'required_lane_compliance ratio mismatch',
      expectedPath: '/agentPrAssurance/metrics/required_lane_compliance/ratio',
      expectedKeyword: 'metric_ratio_mismatch',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { required_lane_compliance: { ratio: number } };
          }
        ).metrics.required_lane_compliance;
        metric.ratio = 0.5;
      },
    },
    {
      name: 'required_lane_compliance required zero with non-null ratio',
      expectedPath: '/agentPrAssurance/metrics/required_lane_compliance/ratio',
      expectedKeyword: 'metric_not_applicable_ratio',
      mutate: (fixture: Record<string, unknown>) => {
        (
          fixture.agentPrAssurance as {
            metrics: {
              required_lane_compliance: {
                satisfied: number;
                required: number;
                ratio: number | null;
                missingLanes: string[];
                notApplicable: boolean;
              };
            };
          }
        ).metrics.required_lane_compliance = {
          satisfied: 0,
          required: 0,
          ratio: 0,
          missingLanes: [],
          notApplicable: true,
        };
      },
    },
    {
      name: 'required_lane_compliance required zero without notApplicable',
      expectedPath: '/agentPrAssurance/metrics/required_lane_compliance/notApplicable',
      expectedKeyword: 'metric_not_applicable_flag',
      mutate: (fixture: Record<string, unknown>) => {
        (
          fixture.agentPrAssurance as {
            metrics: {
              required_lane_compliance: {
                satisfied: number;
                required: number;
                ratio: number | null;
                missingLanes: string[];
              };
            };
          }
        ).metrics.required_lane_compliance = {
          satisfied: 0,
          required: 0,
          ratio: null,
          missingLanes: [],
        };
      },
    },
    {
      name: 'required_lane_compliance required greater than zero with notApplicable',
      expectedPath: '/agentPrAssurance/metrics/required_lane_compliance/notApplicable',
      expectedKeyword: 'metric_not_applicable_flag',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { required_lane_compliance: { notApplicable: boolean } };
          }
        ).metrics.required_lane_compliance;
        metric.notApplicable = true;
      },
    },
    {
      name: 'evidence_completeness present greater than required',
      expectedPath: '/agentPrAssurance/metrics/evidence_completeness/present',
      expectedKeyword: 'metric_count_order',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { evidence_completeness: { present: number } };
          }
        ).metrics.evidence_completeness;
        metric.present = 7;
      },
    },
    {
      name: 'evidence_completeness ratio mismatch',
      expectedPath: '/agentPrAssurance/metrics/evidence_completeness/ratio',
      expectedKeyword: 'metric_ratio_mismatch',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { evidence_completeness: { ratio: number } };
          }
        ).metrics.evidence_completeness;
        metric.ratio = 0.8;
      },
    },
    {
      name: 'false_block_rate annotated false blocks greater than total blocks',
      expectedPath: '/agentPrAssurance/metrics/false_block_rate/annotatedFalseBlocks',
      expectedKeyword: 'metric_count_order',
      mutate: (fixture: Record<string, unknown>) => {
        (
          fixture.agentPrAssurance as {
            metrics: {
              false_block_rate: {
                annotatedFalseBlocks: number;
                totalBlocks: number;
                ratio: number;
                annotationRequired: boolean;
              };
            };
          }
        ).metrics.false_block_rate = {
          annotatedFalseBlocks: 2,
          totalBlocks: 1,
          ratio: 1,
          annotationRequired: false,
        };
      },
    },
    {
      name: 'false_block_rate numeric ratio mismatch',
      expectedPath: '/agentPrAssurance/metrics/false_block_rate/ratio',
      expectedKeyword: 'metric_ratio_mismatch',
      mutate: (fixture: Record<string, unknown>) => {
        (
          fixture.agentPrAssurance as {
            metrics: {
              false_block_rate: {
                annotatedFalseBlocks: number;
                totalBlocks: number;
                ratio: number;
                annotationRequired: boolean;
              };
            };
          }
        ).metrics.false_block_rate = {
          annotatedFalseBlocks: 1,
          totalBlocks: 2,
          ratio: 1,
          annotationRequired: false,
        };
      },
    },
    {
      name: 'false_block_rate unannotated metric with non-null ratio',
      expectedPath: '/agentPrAssurance/metrics/false_block_rate/ratio',
      expectedKeyword: 'metric_unannotated_ratio',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { false_block_rate: { ratio: number | null } };
          }
        ).metrics.false_block_rate;
        metric.ratio = 0;
      },
    },
    {
      name: 'false_block_rate unannotated metric without annotationRequired',
      expectedPath: '/agentPrAssurance/metrics/false_block_rate/annotationRequired',
      expectedKeyword: 'metric_annotation_required',
      mutate: (fixture: Record<string, unknown>) => {
        const metric = (
          fixture.agentPrAssurance as {
            metrics: { false_block_rate: { annotationRequired?: boolean } };
          }
        ).metrics.false_block_rate;
        delete metric.annotationRequired;
      },
    },
  ])('rejects semantic inconsistency: $name', ({ mutate, expectedPath, expectedKeyword }) => {
    const invalidFixture = structuredClone(agentPrAssuranceFixture);

    mutate(invalidFixture);

    expectSemanticError(invalidFixture, expectedPath, expectedKeyword);
  });

  it('rejects missing lanes when required lane compliance is fully satisfied', () => {
    const invalidFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: {
        metrics: {
          required_lane_compliance: {
            satisfied: number;
            required: number;
            ratio: number;
            missingLanes: string[];
          };
        };
      };
    };

    invalidFixture.agentPrAssurance.metrics.required_lane_compliance = {
      satisfied: 4,
      required: 4,
      ratio: 1,
      missingLanes: ['model'],
    };

    expectSemanticError(
      invalidFixture as unknown as Record<string, unknown>,
      '/agentPrAssurance/metrics/required_lane_compliance/missingLanes',
      'metric_missing_lanes_contradiction',
    );
  });

  it('defines zero-denominator behavior for ratio metrics', () => {
    const zeroDenominatorFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: {
        metrics: {
          claim_coverage: {
            numerator: number;
            denominator: number;
            ratio: number;
          };
          evidence_completeness: {
            present: number;
            required: number;
            ratio: number;
            missingArtifacts: string[];
          };
          false_block_rate: {
            annotatedFalseBlocks: number;
            totalBlocks: number;
            ratio: null;
            annotationRequired: boolean;
          };
        };
      };
    };

    zeroDenominatorFixture.agentPrAssurance.metrics.claim_coverage = {
      numerator: 0,
      denominator: 0,
      ratio: 1,
    };
    zeroDenominatorFixture.agentPrAssurance.metrics.evidence_completeness = {
      present: 0,
      required: 0,
      ratio: 1,
      missingArtifacts: [],
    };
    zeroDenominatorFixture.agentPrAssurance.metrics.false_block_rate = {
      annotatedFalseBlocks: 0,
      totalBlocks: 0,
      ratio: null,
      annotationRequired: false,
    };

    const validate = compileSchema();

    expect(validate(zeroDenominatorFixture), JSON.stringify(validate.errors)).toBe(true);
    expect(validateAgenticMetricsSemantics(zeroDenominatorFixture as unknown as Record<string, unknown>)).toEqual([]);
  });

  it('rejects numeric false block rates when totalBlocks is zero', () => {
    const invalidFixture = structuredClone(agentPrAssuranceFixture) as {
      agentPrAssurance: {
        metrics: {
          false_block_rate: {
            annotatedFalseBlocks: number;
            totalBlocks: number;
            ratio: number;
            annotationRequired: boolean;
          };
        };
      };
    };

    invalidFixture.agentPrAssurance.metrics.false_block_rate = {
      annotatedFalseBlocks: 0,
      totalBlocks: 0,
      ratio: 0,
      annotationRequired: false,
    };

    expectSemanticError(
      invalidFixture as unknown as Record<string, unknown>,
      '/agentPrAssurance/metrics/false_block_rate/ratio',
      'metric_zero_denominator_ratio',
    );
  });
});
