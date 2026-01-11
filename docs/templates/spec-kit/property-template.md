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
```ts
import fc from 'fast-check';

const genInput = fc.record({
  // TODO: add fields
});

test('property: <property-id>', () => {
  fc.assert(
    fc.property(genInput, (input) => {
      // Act
      // TODO: call the system under test with `input`, e.g.:
      // const result = myFunctionUnderTest(input);
      const result = input;

      // Assert
      // TODO: replace with meaningful property-specific assertions
      expect(result).toBeDefined();
    })
  );
});
```

## Notes
- Keep the generator small first; expand with edge cases later.
- Prefer shrinking-friendly data shapes.
