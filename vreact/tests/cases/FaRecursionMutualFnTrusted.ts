// expect: reject mutually recursive declarations are not supported
// Also when one of them is @trusted: the cycle check reads its body too.
import { type int } from "vreact/spec";
/** @trusted */
export function f(x: int): int { return x <= 0 ? 0 : g(x - 1); }
export function g(x: int): int { return f(x); }
