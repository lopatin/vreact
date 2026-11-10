// expect: synth write post.status=skipped both.status=skipped check.status=skipped inc=x~+~1 out=a~hole~inside~ensures(…) out=a~hole~inside~assert(…) written=ensures((r:~int)~=>~hole<boolean>()); written=assert(hole<boolean>()); written=return~hole<int>(); written=return~x~+~1;
// synth-r1-2 / contracts-r1-6: a hole in an ensures was filled with `true` (the postcondition
// erased), a hole in an assert likewise. Holes inside requires/ensures/invariant/decreases/
// callbackRequires/assert/assume are never filled, and the other holes of their function are not
// searched (both); holes of the other functions are filled as before (inc).
import { requires, ensures, assert, hole, type int } from "vreact/spec";

export function post(x: int): int {
  ensures((r: int) => hole<boolean>());
  return x;
}

export function both(x: int): int {
  ensures((r: int) => r > x && hole<boolean>());
  return hole<int>();
}

export function check(x: int): int {
  assert(hole<boolean>());
  return x;
}

export function inc(x: int): int {
  requires(x >= 0);
  ensures((r: int) => r === x + 1);
  return hole<int>();
}
