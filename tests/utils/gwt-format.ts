export function formatGWT(given: string, when: string, then: string): string {
  return [`Given ${given}`, `When ${when}`, `Then ${then}`].join(' | ');
}

