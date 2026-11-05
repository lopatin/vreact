// expect: verified
// Integer arithmetic below zero, literal arrays folded with two accumulators, unused / reassigned
// null locals: all typed in Lean (Int, List Int, Option Int).
import { ensures, type int } from "vreact/spec";

export function below(): int {
  ensures((r: int) => r === 1);
  const a = 2;
  const b = 3;
  return a - b < 0 ? 1 : 0;
}

export function sumAndCount(): int {
  ensures((r: int) => r === 32);
  let s = 0;
  let c = 0;
  for (const x of [10, 20]) {
    s = s + x;
    c = c + 1;
  }
  return s + c;
}

export function unusedNull(): int {
  const unused: int | null = null;
  return 0;
}

export function reset(p: int | null): int {
  ensures((r: int) => r === 0);
  let x: int | null = p;
  if (x !== null) {
    x = null;
  }
  return x ?? 0;
}
