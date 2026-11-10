// expect: fail nonzero-divisor f=incomplete
// implies(a, b) is a function call (vreact/spec: `return !a || b`), and requires(c) evaluates c
// at every call (also with checking off): b runs whatever a is. g calls f(1, 0), which meets
// `implies(b !== 0, …)` vacuously, and f throws "idiv by zero" evaluating its own precondition,
// so the divisor obligation in b must not assume b !== 0 (`b === 0 || idiv(a, b) >= 0` guards it).
import { requires, ensures, implies, idiv, type int } from "vreact/spec";

export function f(a: int, b: int): int {
  requires(implies(b !== 0, idiv(a, b) >= 0));
  return 0;
}

export function g(): int {
  ensures((r: int) => r === 0);
  return f(1, 0);
}
