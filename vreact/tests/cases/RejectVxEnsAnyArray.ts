// expect: reject `r` has TypeScript type any, so TypeScript does not check it against the type `readonly (number | null)[]`
// The kinds of the elements of an array count too.
import { ensures, implies, type int } from "vreact/spec";
export function allNull(xs: readonly (int | null)[]): boolean {
  return xs.every((x) => x === null);
}
export function f(n: int): readonly (int | undefined)[] {
  ensures((r) => allNull(r));
  return [undefined];
}
