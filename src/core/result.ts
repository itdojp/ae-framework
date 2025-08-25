export type Ok<T> = { ok: true; value: T };
export type Err<E extends { code: string }> = { ok: false; error: E };
export type Result<T, E extends { code: string } = { code: string; message?: string }> = Ok<T> | Err<E>;

export const ok = <T>(value: T): Ok<T> => ({ ok: true, value });
export const err = <E extends { code: string }>(e: E): Err<E> => ({ ok: false, error: e });

export function isOk<T, E extends { code: string }>(r: Result<T, E>): r is Ok<T> {
  return r.ok;
}

export function isErr<T, E extends { code: string }>(r: Result<T, E>): r is Err<E> {
  return !r.ok;
}

export function unwrap<T, E extends { code: string }>(r: Result<T, E>): T {
  if (isErr(r)) throw new Error(r.error.code);
  return r.value;
}