// expect: verified
// V7 (N11 residual): the enum case split on a field of a field (`o.inner.mode`).
import { ensures, type int } from "vreact/spec";

type St = { mode: "a" | "b" | "c"; n: int };
type Outer = { inner: St; k: int };
export function nestedEnum(o: Outer): int {
  ensures((r: int) => (o.inner.mode === "a" && r === 1) || (o.inner.mode === "b" && r === 2) || (o.inner.mode === "c" && r === 3));
  if (o.inner.mode === "a") return 1;
  if (o.inner.mode === "b") return 2;
  return 3;
}
type Deep = { o: Outer };
export function deepEnum(d: Deep): int {
  ensures((r: int) => (d.o.inner.mode === "a" && r === d.o.k) || (d.o.inner.mode !== "a" && r === 0));
  return d.o.inner.mode === "a" ? d.o.k : 0;
}
