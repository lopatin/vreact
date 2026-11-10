// expect: synth write half.status=skipped unchanged out=a~hole~inside~requires(…)~is~part~of~the~contract~of~half noout=proved~by~Lean
// synth-r1-2 / contracts-r1-6: a hole inside the function's own contract was filled like an
// implementation hole and proved against the contract it is part of: the untestable candidate
// `false` for `requires(hole<boolean>())` was "✔ proved by Lean" and written with --write, after
// which every caller (callHalf) fails. Synth never fills a hole inside a contract: the function is
// not searched, nothing is written.
import { requires, ensures, hole, type int } from "vreact/spec";

export function half(x: int): int {
  requires(hole<boolean>());
  ensures((r: int) => r + r === x);
  return x - x + 3;
}

export function callHalf(): int {
  return half(6);
}
