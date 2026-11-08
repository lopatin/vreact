// expect: status verdict=not-verified errors=internal open=verified some=verified show=verified after=incomplete callAfter=incomplete proved=5 unchecked=2
// Functions named open/some/show and locals named end/def/section/namespace become `open'`,
// `end'`, … in Lean; a let-chain puts `end')` or `namespace')` at the start of a line. The
// report's reading of the generated file must not take them for `end`/`namespace` commands
// (before: the namespace stack was popped/pushed there, so the declarations below were
// named `).after`, …, and an error in `after` was not seen as after's: smuggled/Base.lean,
// a proof file the whitelist rejects put in place after the translation, pre-declares `VTS.kw.after`, the generated one is never added, and after was VERIFIED).
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
