// expect: verified
// N18: `%` with a variable divisor (the carousel wrap-around). VTS `%` is the ECMA remainder:
// the result has the sign of the dividend, so a non-negative dividend and a positive divisor
// give `0 <= r < divisor` (JS.rem.post, and `emod` ranges for grind).
import { useState } from "react";
import { invariant, requires, ensures, type int } from "vreact/spec";

export function nextIdx(xs: readonly int[], sel: int): int {
  requires(xs.length >= 2 && 0 <= sel && sel < xs.length);
  return xs[(sel + 1) % xs.length];
}

export function modRange(n: int, s: int): int {
  requires(n > 0 && 0 <= s);
  ensures((r: int) => 0 <= r && r < n);
  return (s + 1) % n;
}

// a negative dividend: the remainder is in (-n, 0]
export function negRange(n: int, s: int): int {
  requires(n > 0 && s < 0);
  ensures((r: int) => -n < r && r <= 0);
  return s % n;
}

// a negative divisor: only its magnitude matters
export function negDivisor(n: int, s: int): int {
  requires(n < 0 && 0 <= s);
  ensures((r: int) => 0 <= r && r < -n);
  return s % n;
}

export function Carousel() {
  const [slides, setSlides] = useState<readonly string[]>(["a", "b", "c"]);
  const [i, setI] = useState<int>(0);
  invariant(slides.length > 0 && 0 <= i && i < slides.length);
  return (
    <div>
      <p>{slides[i]}</p>
      <button onClick={() => setI((i + 1) % slides.length)}>next</button>
      <button onClick={() => setI((i + slides.length - 1) % slides.length)}>prev</button>
      <button onClick={() => { setSlides([...slides, "n"]); setI(slides.length); }}>add</button>
    </div>
  );
}
