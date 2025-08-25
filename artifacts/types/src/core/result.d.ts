export type Ok<T> = {
    ok: true;
    value: T;
};
export type Err<E extends {
    code: string;
}> = {
    ok: false;
    error: E;
};
export type Result<T, E extends {
    code: string;
} = {
    code: string;
    message?: string;
}> = Ok<T> | Err<E>;
export declare const ok: <T>(value: T) => Ok<T>;
export declare const err: <E extends {
    code: string;
}>(e: E) => Err<E>;
export declare function isOk<T, E extends {
    code: string;
}>(r: Result<T, E>): r is Ok<T>;
export declare function isErr<T, E extends {
    code: string;
}>(r: Result<T, E>): r is Err<E>;
export declare function unwrap<T, E extends {
    code: string;
}>(r: Result<T, E>): T;
