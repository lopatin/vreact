// expect: reject `@ts-ignore` is not supported
// <bUTTON> is an error for TypeScript (no such intrinsic element) unless silenced; an HTML
// document lower-cases the name, so it is a submit button: one click runs onClick and the
// form's onSubmit in one batch. VTS relies on TypeScript's checks, so a directive that silences
// them is rejected.
import { useState } from "react";
import { invariant } from "vreact/spec";

const XS: readonly string[] = ["x", "y"];

export function RjTsIgnore() {
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
        {/* @ts-ignore */}
        <bUTTON
          onClick={() => {
            if (a + b === 0) setB(1);
          }}
        />
      </form>
      <p>{XS[a + b].length}</p>
    </div>
  );
}
