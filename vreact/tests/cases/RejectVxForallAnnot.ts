// expect: reject parameter `i` is annotated `int | null` but receives a value of type `int`
// A quantifier's index is an int.
import { ensures, forall, type int } from "vreact/spec";
export function f(n: int): boolean {
  ensures((r: boolean) => forall(0, n, (i: int | null) => i !== null));
  return true;
}
