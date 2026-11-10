// expect: verified
// Optional expected types: arithmetic and concatenation at T then wrapped, nested ternaries ending
// in null, `x.id === sel` with an optional sel, `??` chains, narrowing by assignment.
import { useState } from "react";
import { ensures, implies, type int } from "vreact/spec";

type Row = { readonly id: int; readonly on: boolean };

export function firstPlusOne(xs: readonly int[]): int | null {
  ensures((r: int | null) => implies(xs.length === 0, r === null));
  return xs.length > 0 ? xs[0] + 1 : null;
}

export function next(p: int): int | null {
  ensures((r: int | null) => r === p + 1);
  const r: int | null = p + 1;
  return r;
}

export function greet(name: string): string | null {
  return "Hello, " + name;
}

export function msg(n: int): string | null {
  ensures((r: string | null) => implies(n >= 0 && n <= 100, r === null));
  const m = n < 0 ? "negative" : n > 100 ? "too big" : null;
  return m;
}

export function mark(xs: readonly Row[], sel: int | null): readonly Row[] {
  return xs.map((x) => (x.id === sel ? { ...x, on: true } : x));
}

export function pick(a: int | null, b: int | null): int {
  ensures((r: int) => implies(a === null && b !== null, r === b));
  return a ?? b ?? 0;
}

export function orZero(p: int | null): int {
  ensures((r: int) => r >= 1 || p !== null);
  let x: int | null = p;
  if (x === null) {
    x = 0;
  }
  return x + 1;
}

export function Picker() {
  const [sel, setSel] = useState<int | null>(null);
  return <button onClick={() => setSel(sel === null ? 0 : sel + 1)}>{sel}</button>;
}
