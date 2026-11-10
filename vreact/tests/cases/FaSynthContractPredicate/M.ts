// expect: synth post.status=skipped okInput.status=skipped succ=x~+~1 out=post~has~no~ensures~and~the~ensures(…)~of~half~calls~it out=okInput~has~no~ensures~and~the~requires(…)~of~half~calls~it noout=proved~by~Lean:~true
// synth round 2: synth refused a hole inside a contract, but filled the same hole one call away:
// post and okInput have no ensures, so their smallest fill `true` was "proved by Lean" (checked
// against nothing) and became half's postcondition and precondition, after which half (which
// returns 3 for every x) verified. A function that a contract depends on and that has no ensures
// of its own is part of the specification: not filled. succ has an ensures: it is filled.
import { requires, ensures, hole, type int } from "vreact/spec";

function okInput(x: int): boolean {
  return hole<boolean>();
}

function post(x: int, r: int): boolean {
  return hole<boolean>();
}

export function half(x: int): int {
  requires(okInput(x));
  ensures((r: int) => post(x, r));
  return x - x + 3;
}

export function callHalf(): int {
  return half(6);
}

function succ(x: int): int {
  ensures((r: int) => r === x + 1);
  return hole<int>();
}

export function viaSucc(x: int): int {
  ensures((r: int) => r === succ(x));
  return x + 1;
}
