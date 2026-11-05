// expect: status mk=incomplete mk2=incomplete pick=verified mode=verified verdict=incomplete errors=none
// Structurally identical inline types of a module are one Lean type: hole<{ readonly v: int }>()
// returned from a function declared to return { readonly v: int } translates (formerly "type
// mismatch: expected MkResult, got Hole"), and so do inline string-literal unions; types first
// met in a body (a local annotation, the hole's type) are emitted with the module's types.
import { ensures, hole, type int } from "vreact/spec";

export function mk(x: int): { readonly v: int } {
  ensures((r: { readonly v: int }) => r.v === x);
  return hole<{ readonly v: int }>();
}

export function mk2(x: int): { readonly w: int } {
  ensures((r: { readonly w: int }) => r.w === x);
  return hole<{ readonly w: int }>();
}

export function pick(m: "a" | "b"): "b" | "a" {
  ensures((r: "a" | "b") => r === m);
  const x: "a" | "b" = m;
  return x;
}

export function mode(): int {
  ensures((r: int) => r === 1);
  const a: "x" | "y" = "x";
  const b: "p" | "q" = "q";
  return a === "x" && b === "q" ? 1 : 0;
}
