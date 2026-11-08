// expect: verified empties=verified prepended=verified fallback=verified widened=verified colour=verified point=verified wrapped=verified swapped=verified names=verified
// Type-argument inference in VTS types (TypeScript cannot tell int from number): from the
// arguments that have a type of their own, then from the type the result must have, then the
// arguments typed by their parameter ([], null, literals); explicit type arguments where a type
// parameter occurs in the result only. Type parameter names live apart from value names.
import { ensures, type int } from "vreact/spec";

type Color = "red" | "green";
type Pt = { readonly x: int; readonly y: int };

export function emptyOf<T>(): readonly T[] {
  ensures((r: readonly T[]) => r.length === 0);
  return [];
}

export function empties(): int {
  ensures((r: int) => r === 0);
  const xs: readonly int[] = emptyOf(); // from the result type
  const ys = emptyOf<string>(); // explicit
  return xs.length + ys.length + emptyOf<Pt>().length;
}

export function prepend<T>(xs: readonly T[], x: T): readonly T[] {
  ensures((r: readonly T[]) => r.length === xs.length + 1);
  return [x, ...xs];
}

export function prepended(): int {
  ensures((r: int) => r === 3);
  return prepend([], 3)[0]; // T = int from 3, then [] at readonly int[]
}

export function orElse<T>(x: T | null, d: T): T {
  if (x === null) return d;
  return x;
}

export function fallback(a: int | null): int {
  ensures((r: int) => a === null ? r === 5 : r === a);
  return orElse(a, 5) + orElse(null, 0);
}

export function pair<T>(a: T, b: T): readonly T[] {
  return [a, b];
}

export function widened(): number {
  return pair(1, 2.5)[0]; // T = number: 1 is widened
}

export function choose<T>(c: boolean, x: T, y: T): T {
  return c ? x : y;
}

export function colour(c: boolean): Color {
  ensures((r: Color) => c ? r === "red" : r === "green");
  const k: Color = choose(c, "red", "green"); // T = Color from the result type
  return k;
}

export function same<T>(x: T): T {
  return x;
}

export function point(): int {
  ensures((r: int) => r === 3);
  const p: Pt = same({ x: 1, y: 2 });
  return p.x + p.y;
}

export function single<U>(x: U): readonly U[] {
  ensures((r: readonly U[]) => r.length === 1);
  return [x];
}

export function wrapped<V>(x: V): readonly V[] {
  ensures((r: readonly V[]) => r.length === 2);
  return [...single<V>(x), ...single(x)];
}

export function swap<A, B>(p: [A, B]): [B, A] {
  return [p[1], p[0]];
}

export function swapped(): int {
  ensures((r: int) => r === 7);
  const q = swap<string, int>(["a", 7]);
  return q[0] + swap([2, "b"])[0].length * 0;
}

// a type parameter named like the value parameter, like a Lean name, and like a generated name
export function sameName<x>(x: x): x {
  return x;
}
export function idList<List, E>(xs: readonly List[], e: E): readonly List[] {
  return xs;
}
export function names(): int {
  ensures((r: int) => r === 2);
  return sameName(1) + idList([1], "e").length;
}
