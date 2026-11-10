// expect: verified Track=verified
// Focus tracking on an autoFocus input, and an element around it whose onBlur updates state,
// are accepted when no render of the component after its first mounts an autoFocus element:
// the input is written in the component's only return, not under a condition, with no key on it
// or around it, and the component renders no other component. React focuses the input in the
// commit that mounts the component; onFocus runs there and its update is committed at once, but
// that commit only re-renders Track (focus handlers are robust: no parent callbacks), keeps the
// input (the `{focused && …}` child before it keeps its index) and focuses nothing, so the chain
// ends (react-dom 18.3.1: one focus() call, no error). The fix of effects-r2-2 rejected these
// handlers on every autoFocus element and every element around one (attack-1 f4); a component
// that may mount an autoFocus element again still may not (FaDomAutoFocusAroundBlur).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

export function Track() {
  const [focused, setFocused] = useState<boolean>(false);
  const [left, setLeft] = useState<int>(0);
  invariant(left >= 0);
  return (
    <div onBlur={() => setLeft((m) => m + 1)}>
      {focused && <p>typing</p>}
      <input autoFocus onFocus={() => setFocused(true)} onBlur={() => setFocused(false)} />
      <p>
        {focused ? "typing" : "idle"} {left}
      </p>
    </div>
  );
}
