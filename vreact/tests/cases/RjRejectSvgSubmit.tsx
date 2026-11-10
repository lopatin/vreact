// expect: reject <input> inside <svg> is an SVG element named input
// The "checkbox" inside <svg> is an SVG element with no type: it does not stop the activation
// of the enclosing submit button, so one click runs onClick and onSubmit in one batch
// (a + b = 2, XS[2] is undefined).
import { useState } from "react";
import { invariant } from "vreact/spec";

const XS: readonly string[] = ["x", "y"];

export function RjSvgSubmit() {
  const [a, setA] = useState(0);
  const [b, setB] = useState(0);
  invariant(a >= 0 && b >= 0 && a + b <= 1);
  return (
    <div>
      <form
        onSubmit={(e) => {
          e.preventDefault();
          if (a + b === 0) setA(1);
        }}
      >
        <button type="submit">
          <svg width="10" height="10">
            <input
              type="checkbox"
              onClick={() => {
                if (a + b === 0) setB(1);
              }}
            />
          </svg>
        </button>
      </form>
      <p>{XS[a + b].length}</p>
    </div>
  );
}
