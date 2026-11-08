// expect: fail postcondition verdict=not-verified same=incomplete proved=0 failed=1
// The build logs in the project's build directory are not evidence (round-2 finding
// r4-lean-r2-cache-poison). When a module is up to date, lake replays the log it stored with it
// (`.vreact/.lake/build/lib/lean/VTS/m/Posts.trace`) instead of running Lean; its input hashes do
// not cover the log. Rewriting that log (failure → `vreact:ok`, no `sorry` warning, clean axioms:
// what a committed `.vreact/`, a shared cache or an agent editing build files could do) made the
// second verify of this project ✔ VERIFIED with no Lean run. Now vreact keeps a record of the
// build directory it left (hashes of every file, outside the project): a build directory that is
// not exactly that one is removed and everything is built again, and a module's messages come
// only from a log of its current inputs. The case is verified, the logs doctored (file POISON),
// and verified again: both reports must say NOT VERIFIED.
import { ensures, type int } from "vreact/spec";

// false: same(0) is 0, not 1
export function same(x: int): int {
  ensures((r: int) => r === x + 1);
  return x;
}
