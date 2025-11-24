import fc from 'fast-check';

export const defaultRuns = 20;

export const reservationArb = fc.record({
  sku: fc.string({ minLength: 3, maxLength: 12 }),
  quantity: fc.integer({ min: 1, max: 5 }),
  requestId: fc.uuid(),
  userId: fc.constantFrom('u1', 'u2', 'u3'),
});

export const insufficientArb = fc.record({
  sku: fc.string({ minLength: 3, maxLength: 12 }),
  stock: fc.integer({ min: 0, max: 2 }),
  userId: fc.constantFrom('u1', 'u2', 'u3'),
});
