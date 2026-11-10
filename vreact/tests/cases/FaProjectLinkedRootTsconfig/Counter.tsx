// expect: reject src/Counter.tsx: the project has no tsconfig.json, so VTS checks src/Counter.tsx with vreact's default options, but the bundler compiles it with the settings of
// The project (no tsconfig.json of its own) is reached through a symbolic link, and a
// tsconfig.json is above its real location (not above the link): Vite looks for the tsconfig of
// a module from its real path and compiles src/Counter.tsx with that one's jsxImportSource
// "/rt", while vreact checks it with its default options. (The harness: VIA_LINK.)
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < 3) setN(n + 1); }}>{n}</button>;
}
