// expect: reject is annotated `S` but receives a value of type `R`
// A record annotation with another field kind (S.v: int | null, R.v?: int) is not the return
// type either, though each converts to the other in TypeScript's eyes.
import { ensures, type int } from "vreact/spec";
type R = { readonly v?: int };
type S = { readonly v: int | null };
export function f(): R {
  ensures((r: S) => r.v === null);
  return {};
}
