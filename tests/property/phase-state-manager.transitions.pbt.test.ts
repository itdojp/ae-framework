import { describe, it, expect } from 'vitest';
import { PhaseStateManager, PhaseType } from '../../src/utils/phase-state-manager';
import fc from 'fast-check';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';

describe('PBT: PhaseStateManager transitions and invariants', () => {
  it('cannot approve before complete; can only transition when complete(+approved if required)', async () => {
    await fc.assert(fc.asyncProperty(
      fc.boolean(),
      async (approvalsRequired) => {
        const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'phase-')); 
        const psm = new PhaseStateManager(tmp);
        await psm.initializeProject('p', approvalsRequired);
        // Start intent
        await psm.startPhase('intent');
        // Approve before complete should throw
        let threw = false;
        try { await psm.approvePhase('intent', 'tester'); } catch { threw = true; }
        expect(threw).toBe(true);
        // Complete
        await psm.completePhase('intent', []);
        // If approvals required, cannot transition yet
        const canBefore = await psm.canTransitionToNextPhase();
        if (approvalsRequired) expect(canBefore).toBe(false);
        else expect(canBefore).toBe(true);
        // Approve (if needed)
        if (approvalsRequired) await psm.approvePhase('intent', 'tester');
        const canAfter = await psm.canTransitionToNextPhase();
        expect(canAfter).toBe(true);
      }
    ), { numRuns: 12 });
  });
});

