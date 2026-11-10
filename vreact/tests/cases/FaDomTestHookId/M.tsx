// expect: verified Named=verified next=verified
// runtime-r2-1: vreact/spec's runtime picked synth's test mode with globalThis.__VREACT_TEST__,
// which HTML's named access on Window makes the element with that id (here typed by the user);
// ensures() then ran `t.posts.push` on the element and threw, in the onClick of a VERIFIED
// component. The hook is now under a symbol key (RUNTIME.mjs checks the runtime).
import { ensures, type int } from "vreact/spec";

export function next(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}
