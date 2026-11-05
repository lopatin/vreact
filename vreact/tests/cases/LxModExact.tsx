// expect: verified Carousel=verified
// V3: the exact values of `%` that a carousel needs: `n % n === 0` (from the last slide to the
// first) and `(sel + 1) % n === sel + 1` in the middle (also for a negative dividend).
import { useState } from "react";
import { requires, ensures, invariant, type int } from "vreact/spec";

export function wrapPoint(n: int): int {
  requires(n > 0);
  ensures((r: int) => r === 0);
  return n % n;
}
export function exactNext(sel: int, n: int): int {
  requires(n > 0 && 0 <= sel && sel < n - 1);
  ensures((r: int) => r === sel + 1);
  return (sel + 1) % n;
}
export function wrapLast(sel: int, n: int): int {
  requires(n > 0 && sel === n - 1);
  ensures((r: int) => r === 0);
  return (sel + 1) % n;
}
export function negSmall(a: int, n: int): int {
  requires(n > 0 && -n < a && a <= 0);
  ensures((r: int) => r === a);
  return a % n;
}
export function negDivisor(a: int, n: int): int {
  requires(n < 0 && 0 <= a && a < -n);
  ensures((r: int) => r === a);
  return a % n;
}

export function Carousel() {
  const [i, setI] = useState<int>(0);
  invariant(0 <= i && i < 5);
  return (
    <div>
      <p>{i}</p>
      <button onClick={() => setI((i + 1) % 5)}>next</button>
      <button onClick={() => setI(i === 4 ? (i + 1) % 5 : i + 1)}>next2</button>
    </div>
  );
}
