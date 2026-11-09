// expect: verified
// `xs.includes(null)` / `xs.indexOf(null)` on `(V | null)[]` compares with null only (a present
// value never equals it), so it needs no equality constraint on V, nor primitive elements: it is
// `xs.some((x) => x === null)`. It was rejected ("V has no equality constraint").
import { ensures, type int } from "vreact/spec";

export function hasHole<K extends int | string, V>(m: ReadonlyMap<K, readonly (V | null)[]>, k: K): boolean {
  ensures((r: boolean) => r === (m.get(k) ?? []).some((x) => x === null));
  return (m.get(k) ?? []).includes(null);
}

export type Cell = { readonly v: int };

export function firstHole(xs: readonly (Cell | null)[]): int {
  ensures((r: int) => r === -1 || (r >= 0 && r < xs.length));
  ensures((r: int) => (r === -1) === !xs.some((x) => x === null));
  return xs.indexOf(null);
}

export function noHoles(xs: readonly (Cell | undefined)[]): boolean {
  ensures((r: boolean) => r === xs.every((x) => x !== undefined));
  return !xs.includes(undefined);
}

export function holesIn<V>(xs: readonly (V | null)[]): boolean {
  ensures((r: boolean) => !r || xs.length > 0);
  ensures((r: boolean) => !xs.includes(null) || r);
  return xs.includes(null);
}
