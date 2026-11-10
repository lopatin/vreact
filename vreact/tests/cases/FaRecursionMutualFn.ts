// expect: reject mutually recursive declarations are not supported
// Two functions that call each other are recursion (the self-call check sees only a function
// calling itself; the cycle check of the declaration order sees this one).
import { type int } from "vreact/spec";
export function f(x: int): int { return x <= 0 ? 0 : g(x - 1); }
export function g(x: int): int { return f(x); }
