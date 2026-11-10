// expect: status verdict=not-verified errors=proof sq=incomplete why.sq=kernel~re-check proved=0 unchecked=1
// The kernel re-check of the built modules (backstop of round-2 finding
// r4-lean-r2-grind-setoption). smuggled/m.lean (put in place after the translation: the whitelist
// rejects it, RejectRlGrindOption) proves `False` with `debug.skipKernelTC` set in grind's
// interactive mode: `decide +kernel` adds `decide False = true` without the kernel, `helper`
// has no axioms, and the lemma `sq_spec` built on it proves sq's false ensures — Lean reported
// `vreact:ok` and clean axioms, and sq was VERIFIED. After the build, vreact replays every
// declaration of the project into Lean's kernel in a fresh process (`vreact-certify`): the kernel
// rejects the unchecked declaration, Proofs.m is not certified, nor is VTS.m.Posts which imports
// it, so sq is INCOMPLETE and its obligation not counted, whatever Lean printed.
import { ensures, type int } from "vreact/spec";

// false: sq(0) is 0, not 1
export function sq(x: int): int {
  ensures((r: int) => r === x + 1);
  return x * x;
}
