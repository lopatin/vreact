// expect: reject a module-level assert(…) about `K`, an /** @opaque */ constant of another module (consts.ts), is not supported
// A fact is a theorem of its constant's module (VTS.consts.K.post), which cannot see this
// module's `succ`: formerly an internal Lean error ("Unknown identifier VTS.a.succ").
import { type int, ensures, assert } from "vreact/spec";
import { K } from "./consts";

function succ(x: int): int {
  return x + 1;
}

assert(succ(K) === 4);

export function g(): int {
  ensures((r) => r === 4);
  return succ(K);
}
