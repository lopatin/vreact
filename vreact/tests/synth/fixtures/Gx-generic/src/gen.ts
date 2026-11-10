import { ensures, hole, type int } from "vreact/spec";

// unconstrained: tested at int and string elements, proved once for every T
export function push<T>(xs: readonly T[], x: T): readonly T[] {
  ensures((r: readonly T[]) => r.length === xs.length + 1);
  return hole<readonly T[]>();
}

// an equality constraint: the contract compares values of K
export function withKey<K extends int | string>(xs: readonly K[], k: K): readonly K[] {
  ensures((r: readonly K[]) => r.includes(k) && r.length === xs.length + 1);
  return hole<readonly K[]>();
}

// a field constraint: x.id is in scope, tested with a witness record
export function idOf<T extends { readonly id: int }>(x: T, d: int): int {
  ensures((r: int) => r === x.id);
  return hole<int>();
}
