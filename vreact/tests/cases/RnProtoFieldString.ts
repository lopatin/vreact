// expect: reject a field named `__proto__` is not supported
// The same with a string key, inside a union variant: `{ kind: "a", "__proto__": 5 }` sets the
// prototype as well.
import { type int, ensures } from "vreact/spec";

type U = { readonly kind: "a"; readonly "__proto__": int } | { readonly kind: "b" };

export function f(u: U): int {
  ensures((r) => r >= 0);
  return u.kind === "a" ? 1 : 0;
}
