// expect: status verdict=not-verified errors=internal open=incomplete some=incomplete show=incomplete why.open=kernel~re-check after=incomplete callAfter=incomplete proved=0 unchecked=7
// Functions named open/some/show and locals named end/def/section/namespace become `open'`,
// `end'`, … in Lean; a let-chain puts `end')` or `namespace')` at the start of a line. The
// report's reading of the generated file must not take them for `end`/`namespace` commands
// (before: the namespace stack was popped/pushed there, so the declarations below were
// named `).after`, …, and an error in `after` was not seen as after's: smuggled/Base.lean,
// a proof file the whitelist rejects put in place after the translation, pre-declares `VTS.kw.after`, the generated one is never added, and after was VERIFIED).
// Round 2 (r4-lean-r2): the kernel re-check finds that Proofs.Base declares the definition
// `VTS.kw.after`: it and every module importing it are not certified, so open/some/show (VERIFIED
// before) are not either — they were elaborated after a user proof that changed the environment
// beyond lemmas (the old expectation was wrong there). The reading of escaped keywords is also
// checked by the suite's leanDecls unit check.
import { ensures, requires, type int } from "vreact/spec";
export function open(x: int): int {
  ensures((r: int) => r === x + 1);
  const end = x + 1;
  return end;
}
export function some(x: int): int {
  ensures((r: int) => r >= x);
  const def = x;
  const section = def + 1;
  return section;
}
export function show(xs: readonly int[]): int {
  requires(xs.length > 0);
  ensures((r: int) => r === xs[0]);
  const namespace = xs[0];
  return namespace;
}
export function after(x: int): int {
  ensures((r: int) => r > x);
  return open(x) - 2;
}
export function callAfter(x: int): int {
  ensures((r: int) => r > x);
  return after(x);
}
