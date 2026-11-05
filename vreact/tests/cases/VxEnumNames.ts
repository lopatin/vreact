// expect: verified
// Enum members are any strings: constructor names are escaped injectively (members that collide
// after priming, `»`, lone surrogates, the empty string, `'`, Lean tokens and generated names)
// and the Lean source stays valid UTF-8.  An enum member is also its string (return, ===).
import { ensures, implies, type int } from "vreact/spec";
type K = "rec" | "rec'" | "mk" | "mk'" | "a»b" | "\uD800" | "\uDC00" | "" | "a\\u0027" | "a'" | "ofNat" | "fun" | "«x»" | "/-⟦ob1⟧-/" | "a\nb" | "😀" | "x.y";
export function f(k: K): int {
  ensures((r: int) => implies(k === "rec'", r === 2) && implies(k === "\uDC00", r === 6) && implies(k === "a'", r === 9));
  switch (k) {
    case "rec": return 1;
    case "rec'": return 2;
    case "mk": return 3;
    case "mk'": return 4;
    case "a»b": return 5;
    case "\uDC00": return 6;
    case "\uD800": return 7;
    case "": return 8;
    case "a'": return 9;
    case "a\\u0027": return 10;
    default: return 0;
  }
}
export function g(k: K): string {
  ensures((r: string) => implies(k === "\uD800", r === "\uD800") && implies(k === "a»b", r === "a»b") && implies(k === "", r === ""));
  return k;
}
export function same(k: K, s: string): boolean {
  ensures((r: boolean) => implies(k === "rec'" && s === "rec'", r));
  return k === s;
}
