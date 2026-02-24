import type { ValidationInput } from './validation-task-adapter.types.js';

export interface TraceabilityMatrixRow {
  requirementId: string;
  tests: string[];
  code: string[];
  diagramId: string[];
  morphismId: string[];
  acceptanceTestId: string[];
  hasContextPackColumns: boolean;
  linked: boolean;
}

function toStringArray(input: unknown): string[] {
  if (Array.isArray(input)) {
    return input.filter((value): value is string => typeof value === 'string');
  }
  if (typeof input === 'string' && input.trim().length > 0) {
    return [input.trim()];
  }
  return [];
}

export function extractTraceabilityMatrixRows(input: ValidationInput): TraceabilityMatrixRow[] {
  const rows: TraceabilityMatrixRow[] = [];
  for (const source of input.resolvedSources) {
    let parsed: unknown;
    try {
      parsed = JSON.parse(source.content);
    } catch {
      continue;
    }
    if (!parsed || typeof parsed !== 'object') {
      continue;
    }
    const schemaVersion = (parsed as { schemaVersion?: unknown }).schemaVersion;
    if (schemaVersion !== 'issue-traceability-matrix/v1') {
      continue;
    }
    const candidateRows = (parsed as { rows?: unknown }).rows;
    if (!Array.isArray(candidateRows)) {
      continue;
    }
    for (const row of candidateRows) {
      if (!row || typeof row !== 'object') {
        continue;
      }
      const requirementId = (row as { requirementId?: unknown }).requirementId;
      if (typeof requirementId !== 'string' || requirementId.trim().length === 0) {
        continue;
      }
      const tests = Array.isArray((row as { tests?: unknown }).tests)
        ? ((row as { tests: unknown[] }).tests.filter((value): value is string => typeof value === 'string'))
        : [];
      const code = Array.isArray((row as { code?: unknown }).code)
        ? ((row as { code: unknown[] }).code.filter((value): value is string => typeof value === 'string'))
        : [];
      const hasDiagramId = Object.prototype.hasOwnProperty.call(row, 'diagramId')
        || Object.prototype.hasOwnProperty.call(row, 'diagramIds');
      const hasMorphismId = Object.prototype.hasOwnProperty.call(row, 'morphismId')
        || Object.prototype.hasOwnProperty.call(row, 'morphismIds');
      const hasAcceptanceTestId = Object.prototype.hasOwnProperty.call(row, 'acceptanceTestId')
        || Object.prototype.hasOwnProperty.call(row, 'acceptanceTestIds');
      const diagramId = toStringArray(
        (row as { diagramId?: unknown; diagramIds?: unknown }).diagramId
          ?? (row as { diagramId?: unknown; diagramIds?: unknown }).diagramIds,
      );
      const morphismId = toStringArray(
        (row as { morphismId?: unknown; morphismIds?: unknown }).morphismId
          ?? (row as { morphismId?: unknown; morphismIds?: unknown }).morphismIds,
      );
      const acceptanceTestId = toStringArray(
        (row as { acceptanceTestId?: unknown; acceptanceTestIds?: unknown }).acceptanceTestId
          ?? (row as { acceptanceTestId?: unknown; acceptanceTestIds?: unknown }).acceptanceTestIds,
      );
      const linked = tests.length > 0 && code.length > 0;
      rows.push({
        requirementId: requirementId.trim(),
        tests,
        code,
        diagramId,
        morphismId,
        acceptanceTestId,
        hasContextPackColumns: hasDiagramId || hasMorphismId || hasAcceptanceTestId,
        linked,
      });
    }
  }
  return rows;
}
