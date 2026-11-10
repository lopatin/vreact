// expect: verified PRICES=verified DAYS=verified price=verified days=verified errors=none
import { assert, ensures, type int } from "vreact/spec";

// module-level Maps and Sets: an @opaque one with facts, a transparent one
/** @opaque */
export const PRICES: ReadonlyMap<string, int> = new Map([["a", 1], ["b", 2]]);
assert(PRICES.size === 2 && PRICES.get("a") === 1);

export const DAYS: ReadonlySet<string> = new Set(["mon", "tue", "mon"]);

export function price(k: string): int {
  ensures((r) => k !== "a" || r === 1);
  return PRICES.get(k) ?? 0;
}

export function days(): int {
  ensures((r) => r === 2);
  return DAYS.size;
}
