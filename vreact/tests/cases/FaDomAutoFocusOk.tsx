// expect: verified Form=verified
// Focus handlers may update state on elements that neither have autoFocus nor contain one (the
// element that has focus before an autoFocus element mounts updates once: it does not get focus
// back inside the chain), and on an element whose autoFocus is literally false; an autoFocus
// element's own focus handlers may do what does not update state.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Form() {
  const [s, setS] = useState<string>("");
  const [focused, setFocused] = useState<boolean>(false);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div>
      <input autoFocus value={s} onChange={(e) => setS(e.target.value)} onBlur={() => console.log("left")} />
      <input onFocus={() => setFocused(true)} onBlur={() => setFocused(false)} />
      <input autoFocus={false} onFocus={() => setN((m) => m + 1)} />
      <p>{focused ? "focused" : "idle"}</p>
    </div>
  );
}
