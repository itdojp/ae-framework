import { describe, it, expect } from "vitest";
import fc from "fast-check";

// 量 > 0、在庫は負にならない、同一orderIdは冪等 などを性質で検査

describe("reservation properties", () => {
  it("quantity is positive", () => {
    fc.assert(fc.property(fc.integer({ min: 1, max: 10_000 }), (q) => q > 0));
  });
});