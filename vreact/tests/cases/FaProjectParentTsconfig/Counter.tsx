// expect: reject the project has no tsconfig.json, so VTS checks src/Counter.tsx with vreact's default options, but the bundler compiles it with the settings of
// The project has no tsconfig.json, but vreact/tsconfig.json is above tests/.work: Vite compiles
// the sources with the nearest tsconfig.json above them, which VTS did not read (its defaults).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < 3) setN(n + 1); }}>{n}</button>;
}
