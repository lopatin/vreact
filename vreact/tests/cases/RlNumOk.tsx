// expect: verified ratio=verified band=verified scaled=verified label=verified Meter=verified
// Numbers are an opaque type in Lean (R4 item 13): every number operation still translates —
// literals, int → number, + - * /, unary -, ++, comparisons, ===, switch on a number,
// Math.floor/ceil/round/trunc/abs/max/min (also n-ary), String(x), template literals, JSX text
// and attributes, number state — and what is provable without knowing anything about numbers
// (congruence, int facts, Bool structure) is still proved.
import { useState } from "react";
import { ensures, invariant, requires, type int } from "vreact/spec";

// (a division needs a divisor that is not zero: RlNegZero)
export function ratio(a: int, b: int): boolean {
  requires(b !== 0);
  ensures((r: boolean) => r === (a / b < 0.5));
  return a / b < 0.5;
}

export function band(x: number): int {
  ensures((r: int) => r >= 0 && r <= 3);
  switch (x) {
    case 1.5:
      return 1;
    case -2:
      return 2;
    default:
      return x >= 10 ? 3 : 0;
  }
}

export function scaled(x: number, k: int): number {
  let y = -x * k + 0.25;
  y++;
  const m = Math.max(Math.floor(y), Math.ceil(x), Math.round(y / 2), Math.trunc(x - y));
  return Math.min(Math.abs(m), 1e21);
}

export function label(x: number): string {
  ensures((r: string) => r === `${x} units`);
  return `${x} units`;
}

export function Meter() {
  const [level, setLevel] = useState<number>(0.5);
  const [clicks, setClicks] = useState<int>(0);
  invariant(clicks >= 0);
  return (
    <div>
      <meter value={level} />
      <span>{Math.round(level * 100)}%</span>
      <button onClick={() => { setLevel(level === 1 ? 0 : level * 2); setClicks(clicks + 1); }}>{String(level)}</button>
    </div>
  );
}
