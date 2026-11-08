// expect: reject onChange and onInput on <input> both run on one native "input" event
// The same as RjRejectKelvinEntity with U+212A KELVIN SIGN written as the character (pre-existing): JS's toLowerCase() maps
// it to "checkbox", but HTML matches type keywords ASCII-case-insensitively: this is an invalid
// type, a text input, whose one `input` event runs onInput and onChange in one batch.
import { useState } from "react";
import { invariant } from "vreact/spec";

const XS: readonly string[] = ["x", "y"];

export function RjKelvinLiteral() {
  const [a, setA] = useState(0);
  const [b, setB] = useState(0);
  invariant(a >= 0 && b >= 0 && a + b <= 1);
  return (
    <div>
      <input
        type="checKbox"
        onChange={() => {
          if (a + b === 0) setA(1);
        }}
        onInput={() => {
          if (a + b === 0) setB(1);
        }}
      />
      <p>{XS[a + b].length}</p>
    </div>
  );
}
