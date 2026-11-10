// expect: verified
// In contracts, `||` / `&&` chains (left-associated, 3+ operands), `!(…)`, `implies`
// and `?:` narrow their later operands like `branch` does in code (TypeScript accepts
// all of these): union tags and null tests in a compound left operand.
import { ensures, requires, implies, type int } from "vreact/spec";
type S ={ kind: "editing" } | { kind: "sent"; to: string } | { kind: "draft"; body: string };
// || chains: the right operand narrowed by every earlier operand failing
export function f(s: S, b: boolean): boolean {
  ensures((r: boolean) => b || s.kind === "editing" || s.kind === "draft" || s.to.length >= 0);
  return true;
}
export function g(b: boolean, p: int | null): int {
  ensures((r: int) => b || p === null || r === p + 0 || true);
  return p === null ? 0 : p;
}
// && chains with 3+ operands and null tests
export function h(x: int | null, y: int | null): boolean {
  requires(x !== null && y !== null && x + y >= 0);
  ensures((r: boolean) => x !== null && y !== null && x + y >= 0 && r);
  return true;
}
// negated compound guards
export function k(x: int | null, y: int | null): int {
  ensures((r: int) => !(x === null || y === null) || r === 0);
  ensures((r: int) => implies(x !== null && y !== null, r >= 0 || r < 0));
  ensures((r: int) => (x !== null && y !== null && x >= 0) ? r === x + y : true);
  ensures((r: int) => x === null || y === null ? r === 0 : r === x + y);
  return x === null || y === null ? 0 : x + y;
}
// a later operand that does not need the narrowing keeps the plain form
export function plain(a: int, b: int): boolean {
  ensures((r: boolean) => a > 0 || b > 0 || r === (a <= 0 && b <= 0) || true);
  return a <= 0 && b <= 0;
}
