// expect: reject autoFocus on <input> inside an element with onBlur on <div>, which updates state, and a later render of Two may mount an autoFocus element (its <input autoFocus> on line 16 has a key)
// Each commit mounts the keyed input (focus enters the div) and then the keyed textarea (focus
// leaves the div: its onBlur runs inside the commit and updates n), so the next commit, nested,
// mounts both again: react-dom 18.3.1 throws "Maximum update depth exceeded" from setN after 50
// nested commits. An element around an autoFocus element may update state in a focus handler
// only when no render of its component after the first mounts an autoFocus element
// (FaDomAutoFocusTrack).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Two() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div>
      <div onBlur={() => setN((m) => m + 1)}>
        <input key={n} autoFocus />
      </div>
      <textarea key={n} autoFocus />
      <p>{n}</p>
    </div>
  );
}
