// expect: verified
// Assignment and narrowing: `x = e` with a non-null e narrows x to e (as in TypeScript),
// `x = null` is well-typed, and reassigning a record drops the narrowing of its fields.
import { ensures, type int } from "vreact/spec";

type S = { readonly sel: int | null };

export function ctlBumpedOk(p: int): int {
  ensures((r: int) => r === p + 1);
  let x: int | null = p;
  if (x !== null) {
    x = x + 1;
    return x;
  }
  return p + 1;
}

export function ctlAddNarrowed(p: int): int {
  ensures((r: int) => r === p + 3);
  let x: int | null = p;
  if (x !== null) {
    x += 2;
    x++;
    return x;
  }
  return p + 3;
}

export function ctlResetNull(p: int | null): int {
  ensures((r: int) => r === 0);
  const unused: int | null = null;
  let x: int | null = p;
  if (x !== null) {
    x = null;
  }
  return x === null ? 0 : 1;
}

export function ctlPathNarrow(p: int): int | null {
  ensures((r: int | null) => r === null);
  let s: S = { sel: p };
  if (s.sel !== null) {
    s = { sel: null };
    return s.sel;
  }
  return null;
}
