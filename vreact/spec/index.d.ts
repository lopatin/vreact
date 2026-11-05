/**
 * vreact/spec — contracts for Verified TypeScript (VTS).
 *
 * These functions are checked statically by `vreact verify` (translated to Lean 4
 * proof obligations).  At runtime they are no-ops unless contract checking is
 * enabled with `setContractChecking(true)`, in which case `requires`,
 * `invariant` and `assert` throw on violation (useful for unverified callers).
 */

/** Integers. A type alias of `number` for TypeScript; modelled as Lean `Int`. */
export type int = number;

/** Precondition of a function (first statements of the body) or of a component's props. */
export declare function requires(cond: boolean): void;
/** Postcondition of a function: `ensures(r => …)` (first statements of the body). */
export declare function ensures(post: (result: any) => boolean): void;
/** Component state invariant (after the hooks). Must hold in every reachable state. */
export declare function invariant(cond: boolean): void;
/** Contract of a callback prop: the component promises to call `cb` only with arguments satisfying `pre`. */
export declare function callbackRequires<A extends unknown[]>(cb: (...args: A) => void, pre: (...args: A) => boolean): void;
/** A proof obligation at this program point (also adds the fact for later obligations). */
export declare function assert(cond: boolean): void;
/** A trusted assumption (reported by `vreact verify` as ASSUMES). */
export declare function assume(cond: boolean): void;
/** Termination measure (reserved). */
export declare function decreases(measure: int): void;

/** ∀ i ∈ [lo, hi). p(i) */
export declare function forall(lo: int, hi: int, p: (i: int) => boolean): boolean;
/** ∃ i ∈ [lo, hi). p(i) */
export declare function exists(lo: int, hi: int, p: (i: int) => boolean): boolean;
/** All keys distinct (React list keys, ids, …). */
export declare function distinct<T>(xs: readonly T[], key?: (x: T) => int | string): boolean;
/** a ⇒ b */
export declare function implies(a: boolean, b: boolean): boolean;
/** Floor division Math.floor(a / b) on integers (requires b ≠ 0). */
export declare function idiv(a: int, b: int): int;
/** [0, 1, …, n-1] */
export declare function range(n: int): int[];
/** A placeholder for `vreact synth`. */
export declare function hole<T>(): T;

export declare function setContractChecking(on: boolean): void;
