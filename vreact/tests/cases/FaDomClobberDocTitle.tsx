// expect: reject name="title" on <form>: HTML's named access makes this element the property title of the document
// A form control may be named title (FaDomNamesCommon), but the document shows a <form> by its
// name, and the effect's `document.title = …` is then ignored (Chromium 152 assigns nothing while
// document.title is this form): on the document, title stays reserved, as does body (read by
// react-dom's getActiveElement), while both are accepted on form controls.
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Titled() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    document.title = `clicked ${n}`;
  }, [n]);
  return (
    <form name="title">
      <button type="button" onClick={() => setN(n + 1)}>{n}</button>
    </form>
  );
}
