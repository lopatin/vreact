// expect: fail postcondition ok=verified
// False control for the nested enum split: a wrong arm.
import { ensures, type int } from "vreact/spec";

type St = { mode: "a" | "b" | "c"; n: int };
type Outer = { inner: St; k: int };
export function ok(o: Outer): int {
  ensures((r: int) => (o.inner.mode === "a" && r === 1) || (o.inner.mode !== "a" && r === 2));
  return o.inner.mode === "a" ? 1 : 2;
}
export function wrongArm(o: Outer): int {
  ensures((r: int) => (o.inner.mode === "a" && r === 1) || (o.inner.mode === "b" && r === 2) || (o.inner.mode === "c" && r === 3));
  if (o.inner.mode === "a") return 1;
  if (o.inner.mode === "b") return 3;
  return 3;
}
