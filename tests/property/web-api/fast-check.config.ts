import fc from 'fast-check';

const envRuns = Number.parseInt(
  process.env.FC_WEBAPI_RUNS ?? process.env.FC_NUM_RUNS ?? process.env.FC_RUNS ?? '',
  10,
);
export const defaultRuns = Number.isFinite(envRuns) ? envRuns : 50;

const requestIdArb = fc.uuid();
const skuArb = fc.string({ minLength: 3, maxLength: 12 });
const userIdArb = fc.constantFrom('u1', 'u2', 'u3');

export const reservationArb = fc.record({
  requestId: requestIdArb,
  sku: skuArb,
  quantity: fc.integer({ min: 1, max: 5 }),
  userId: userIdArb,
});

export const insufficientArb = fc.record({
  requestId: requestIdArb,
  sku: skuArb,
  stock: fc.integer({ min: 0, max: 2 }),
  userId: userIdArb,
});
