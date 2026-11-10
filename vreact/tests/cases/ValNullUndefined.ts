// expect: verified
// Strict tests against the nullish value the type actually has, and loose `== null`.
import { ensures, implies, type int } from "vreact/spec";

type Task = { readonly id: int; readonly due?: int };

export function hasNoDue(t: Task): boolean {
  ensures((r) => r === (t.due === undefined));
  return t.due == null;
}

export function isNull(x: int | null): boolean {
  ensures((r: boolean) => r === (x == null));
  return x === null;
}

export function notFound(xs: readonly int[], k: int): boolean {
  ensures((r: boolean) => implies(!xs.includes(k), r));
  return xs.find((x) => x === k) === undefined;
}

export function sameSel(a: int | null, b: int | null): boolean {
  ensures((r: boolean) => implies(a === null && b === null, r));
  return a === b;
}

export function selected(id: int, sel: int | null): boolean {
  ensures((r: boolean) => implies(sel === null, !r));
  return id === sel;
}
