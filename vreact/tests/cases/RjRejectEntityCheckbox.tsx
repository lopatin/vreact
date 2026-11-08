// expect: reject both run on one native "click" event
// JSX decodes character references in attribute strings: type="checkbo&#120;" is a
// checkbox, whose click runs onClick and onChange in one batch (TypeScript's AST holds
// the raw text, which the layout check must not use).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEntityCheckbox() {
  const [n, setN] = useState<int>(0);
  const [on, setOn] = useState<boolean>(false);
  invariant(n >= 0);
  return <input type="checkbo&#120;" checked={on} onClick={() => setN(n + 1)} onChange={() => setOn(!on)} />;
}
