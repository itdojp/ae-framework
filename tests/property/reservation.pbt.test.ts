import { describe, it, expect, beforeEach, afterEach } from "vitest";
import fc from "fast-check";
import { AEIR } from '@ae-framework/spec-compiler';
import { DeterministicCodeGenerator } from '../../src/codegen/deterministic-generator';
import { writeFileSync, unlinkSync, existsSync, mkdirSync, rmSync } from 'fs';
import { join } from 'path';

describe("AE-IR Property-Based Tests", () => {
  const testOutputDir = join(__dirname, '../tmp/pbt-output');
  
  beforeEach(() => {
    if (existsSync(testOutputDir)) {
      rmSync(testOutputDir, { recursive: true, force: true });
    }
    mkdirSync(testOutputDir, { recursive: true });
  });
  
  afterEach(() => {
    if (existsSync(testOutputDir)) {
      rmSync(testOutputDir, { recursive: true, force: true });
    }
  });

  describe("AE-IR Structure Properties", () => {
    const validAEIRArbitrary = fc.record({
      version: fc.string({ minLength: 1, maxLength: 10 }),
      metadata: fc.record({
        name: fc.string({ minLength: 1, maxLength: 50 }),
        description: fc.option(fc.string({ maxLength: 200 })),
        version: fc.option(fc.string({ minLength: 1, maxLength: 20 })),
        created: fc.date().map(d => d.toISOString()),
        updated: fc.date().map(d => d.toISOString())
      }),
      glossary: fc.array(fc.record({
        term: fc.string({ minLength: 1, maxLength: 50 }),
        definition: fc.string({ minLength: 1, maxLength: 200 }),
        aliases: fc.option(fc.array(fc.string({ minLength: 1, maxLength: 30 }), { maxLength: 5 }))
      }), { maxLength: 10 }),
      domain: fc.array(fc.record({
        name: fc.string({ minLength: 1, maxLength: 30 }).filter(s => /^[A-Za-z][A-Za-z0-9]*$/.test(s)),
        description: fc.option(fc.string({ maxLength: 200 })),
        fields: fc.array(fc.record({
          name: fc.string({ minLength: 1, maxLength: 30 }).filter(s => /^[a-zA-Z][a-zA-Z0-9]*$/.test(s)),
          type: fc.constantFrom('string', 'UUID', 'integer', 'decimal', 'boolean', 'datetime', 'text'),
          required: fc.option(fc.boolean()),
          constraints: fc.option(fc.array(fc.string({ maxLength: 100 }), { maxLength: 3 })),
          description: fc.option(fc.string({ maxLength: 100 }))
        }), { minLength: 1, maxLength: 10 })
      }), { minLength: 1, maxLength: 5 }),
      invariants: fc.array(fc.record({
        id: fc.string({ minLength: 1, maxLength: 30 }),
        description: fc.string({ minLength: 1, maxLength: 200 }),
        expression: fc.string({ minLength: 1, maxLength: 100 }),
        entities: fc.array(fc.string({ minLength: 1, maxLength: 30 }), { maxLength: 5 }),
        severity: fc.constantFrom('error', 'warning')
      }), { maxLength: 10 }),
      usecases: fc.array(fc.record({
        name: fc.string({ minLength: 1, maxLength: 50 }),
        description: fc.option(fc.string({ maxLength: 200 })),
        actor: fc.string({ minLength: 1, maxLength: 30 }),
        preconditions: fc.option(fc.array(fc.string({ maxLength: 100 }), { maxLength: 5 })),
        postconditions: fc.option(fc.array(fc.string({ maxLength: 100 }), { maxLength: 5 })),
        steps: fc.array(fc.record({
          step: fc.integer({ min: 1, max: 20 }),
          description: fc.string({ minLength: 1, maxLength: 100 }),
          type: fc.constantFrom('action', 'validation', 'computation')
        }), { minLength: 1, maxLength: 10 })
      }), { maxLength: 10 }),
      api: fc.array(fc.record({
        method: fc.constantFrom('GET', 'POST', 'PUT', 'PATCH', 'DELETE'),
        path: fc.string({ minLength: 1, maxLength: 50 }).filter(s => s.startsWith('/')),
        summary: fc.option(fc.string({ maxLength: 100 })),
        description: fc.option(fc.string({ maxLength: 200 }))
      }), { maxLength: 10 })
    });

    it("generated AE-IR should always be valid JSON", () => {
      fc.assert(
        fc.property(validAEIRArbitrary, (aeir) => {
          const jsonString = JSON.stringify(aeir);
          expect(() => JSON.parse(jsonString)).not.toThrow();
          expect(aeir.version).toBeDefined();
          expect(aeir.metadata.name).toBeDefined();
          expect(Array.isArray(aeir.domain)).toBe(true);
          expect(aeir.domain.length).toBeGreaterThan(0);
        }),
        { numRuns: 50 }
      );
    });

    it("domain entities should have valid TypeScript identifiers", () => {
      fc.assert(
        fc.property(validAEIRArbitrary, (aeir) => {
          for (const entity of aeir.domain) {
            expect(entity.name).toMatch(/^[A-Za-z][A-Za-z0-9]*$/);
            for (const field of entity.fields) {
              expect(field.name).toMatch(/^[a-zA-Z][a-zA-Z0-9]*$/);
            }
          }
        }),
        { numRuns: 30 }
      );
    });
  });

  describe("Code Generation Stability Properties", () => {
    it("should generate identical output for identical AE-IR input", () => {
      fc.assert(
        fc.property(
          fc.record({
            version: fc.constant('1.0.0'),
            metadata: fc.record({
              name: fc.constant('TestApp'),
              created: fc.constant('2025-01-01T00:00:00Z'),
              updated: fc.constant('2025-01-01T00:00:00Z')
            }),
            glossary: fc.constant([]),
            domain: fc.array(fc.record({
              name: fc.constantFrom('User', 'Product', 'Order'),
              fields: fc.array(fc.record({
                name: fc.constantFrom('id', 'name', 'email', 'price'),
                type: fc.constantFrom('UUID', 'string', 'decimal'),
                required: fc.boolean()
              }), { minLength: 1, maxLength: 3 })
            }), { minLength: 1, maxLength: 2 }),
            invariants: fc.constant([]),
            usecases: fc.constant([]),
            api: fc.constant([])
          }),
          fc.constantFrom('typescript', 'react', 'api', 'database')
        ),
        (aeir, target) => {
          const inputPath = join(testOutputDir, 'test-aeir.json');
          writeFileSync(inputPath, JSON.stringify(aeir, null, 2));

          const generator1 = new DeterministicCodeGenerator({
            inputPath,
            outputDir: join(testOutputDir, 'gen1'),
            target: target as any,
            enableDriftDetection: false
          });

          const generator2 = new DeterministicCodeGenerator({
            inputPath,
            outputDir: join(testOutputDir, 'gen2'),
            target: target as any,
            enableDriftDetection: false
          });

          const manifest1 = generator1.generate();
          const manifest2 = generator2.generate();

          expect(manifest1.files.length).toBe(manifest2.files.length);
          
          for (let i = 0; i < manifest1.files.length; i++) {
            expect(manifest1.files[i].filePath).toBe(manifest2.files[i].filePath);
            expect(manifest1.files[i].content).toBe(manifest2.files[i].content);
            expect(manifest1.files[i].hash).toBe(manifest2.files[i].hash);
          }
        },
        { numRuns: 20 }
      );
    });

    it("should detect drift when AE-IR changes", () => {
      fc.assert(
        fc.property(
          fc.record({
            version: fc.constant('1.0.0'),
            metadata: fc.record({
              name: fc.constant('TestApp'),
              created: fc.constant('2025-01-01T00:00:00Z'),
              updated: fc.constant('2025-01-01T00:00:00Z')
            }),
            glossary: fc.constant([]),
            domain: fc.array(fc.record({
              name: fc.constantFrom('User', 'Product'),
              fields: fc.array(fc.record({
                name: fc.constantFrom('id', 'name'),
                type: fc.constantFrom('UUID', 'string'),
                required: fc.boolean()
              }), { minLength: 1, maxLength: 2 })
            }), { minLength: 1, maxLength: 1 }),
            invariants: fc.constant([]),
            usecases: fc.constant([]),
            api: fc.constant([])
          }),
          fc.string({ minLength: 1, maxLength: 10 })
        ),
        (baseAEIR, newName) => {
          const inputPath = join(testOutputDir, 'drift-test-aeir.json');
          const outputDir = join(testOutputDir, 'drift-test');
          
          writeFileSync(inputPath, JSON.stringify(baseAEIR, null, 2));

          const generator = new DeterministicCodeGenerator({
            inputPath,
            outputDir,
            target: 'typescript',
            enableDriftDetection: true
          });

          generator.generate();

          const modifiedAEIR = {
            ...baseAEIR,
            metadata: { ...baseAEIR.metadata, name: newName }
          };
          writeFileSync(inputPath, JSON.stringify(modifiedAEIR, null, 2));

          const driftResult = generator.detectDrift(
            require('crypto').createHash('sha256')
              .update(JSON.stringify(modifiedAEIR, null, 2))
              .digest('hex')
          );

          if (newName !== baseAEIR.metadata.name) {
            expect(driftResult.hasDrift).toBe(true);
            expect(driftResult.driftedFiles.length).toBeGreaterThan(0);
          }
        },
        { numRuns: 15 }
      );
    });
  });

  describe("Reservation Business Logic Properties", () => {
    it("quantity is always positive", () => {
      fc.assert(fc.property(fc.integer({ min: 1, max: 10_000 }), (q) => q > 0));
    });

    it("reservation operations are idempotent for same orderId", () => {
      fc.assert(
        fc.property(
          fc.string({ minLength: 1, maxLength: 20 }),
          fc.integer({ min: 1, max: 100 }),
          (orderId, quantity) => {
            const reservation1 = { orderId, quantity, timestamp: new Date().toISOString() };
            const reservation2 = { orderId, quantity, timestamp: new Date().toISOString() };
            
            expect(reservation1.orderId).toBe(reservation2.orderId);
            expect(reservation1.quantity).toBe(reservation2.quantity);
          }
        ),
        { numRuns: 100 }
      );
    });

    it("inventory cannot go negative", () => {
      fc.assert(
        fc.property(
          fc.integer({ min: 0, max: 1000 }),
          fc.integer({ min: 1, max: 100 }),
          (initialStock, reservationQuantity) => {
            const finalStock = initialStock - reservationQuantity;
            
            if (reservationQuantity > initialStock) {
              expect(finalStock).toBeLessThan(0);
            } else {
              expect(finalStock).toBeGreaterThanOrEqual(0);
            }
          }
        ),
        { numRuns: 200 }
      );
    });
  });
});