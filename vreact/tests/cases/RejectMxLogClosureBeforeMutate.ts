// expect: reject this function refers to `n`, which is mutated after the function is created
import { ensures, type int } from "vreact/spec";

// logging is exempt only where it stands: a helper that logs `n` runs later and would see the
// mutated Map, which its translation (made where it is created) does not
export function build(xs: readonly int[]): int {
  ensures((r) => r >= 0);
  const n = new Map<int, int>();
  const show = () => console.log(n.size + 1);
  for (const x of xs) n.set(x, x);
  return n.size;
}
