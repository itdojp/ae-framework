# Property Spec Template (fast-check)

## Meta
- ID: <property-id>
- Domain: <domain>
- Invariant: <short invariant>
- Risks: <what breaks if violated>

## Property
- Given: <state assumptions>
- When: <operation>
- Then: <invariant/assertion>

## Generator sketch
```ts no-doctest
import fc from 'fast-check';

const genInput = fc.record({
  // NEXT: add fields
});

test('property: <property-id>', () => {
  fc.assert(
    fc.property(genInput, (input) => {
      // Act
      // NEXT: call the system under test with `input`, e.g.:
      // const result = myFunctionUnderTest(input);
      const result = input;

      // Assert
      // NEXT: replace with meaningful property-specific assertions
      expect(result).toBeDefined();
    })
  );
});
```

## Notes
- Keep the generator small first; expand with edge cases later.
- Prefer shrinking-friendly data shapes.
- Define contract IDs and gate/evidence mapping in `dbc-template.md`; keep this template focused on executable property tests.
