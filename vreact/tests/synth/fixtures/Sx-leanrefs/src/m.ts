import { requires, ensures, hole, type int } from "vreact/spec";

// no solution in the grammar (no multiplication): stays a hole
export function sq(x: int): int {
  ensures((r: int) => r === x * x);
  return hole<int>();
}

/** @trusted */
export function viaTrusted(x: int): int {
  ensures((r: int) => r >= 0);
  return sq(x);
}

// the contract mentions only the trusted viaTrusted (an axiom: Lean never sees its body)
export function overTrusted(x: int): int {
  ensures((r: int) => r === x || r === viaTrusted(x) + 1);
  return hole<int>();
}

// only g's own ensures mention sq (a separate theorem): g's definition is x + 1
export function g(x: int): int {
  ensures((r: int) => r === x + 1 || r === sq(x));
  return x + 1;
}

export function overEnsures(x: int): int {
  ensures((r: int) => r === g(x) + 1);
  return hole<int>();
}

// a precondition is part of the function's type, also for a @trusted one: sq is in the statement
/** @trusted */
export function guarded(x: int): int {
  requires(sq(x) >= 0);
  return 0;
}

export function overRequires(x: int): int {
  ensures((r: int) => r === x || r === guarded(x));
  return hole<int>();
}

// the body of a (non-trusted) callee is part of its definition: sq is in the statement
export function sqPlus(x: int): int {
  return sq(x) + 1;
}

export function overBody(x: int): int {
  ensures((r: int) => r === sqPlus(x));
  return hole<int>();
}
