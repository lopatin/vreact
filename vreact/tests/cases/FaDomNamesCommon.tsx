// expect: verified Signup=verified
// Common field names are accepted although they are properties of forms or of the document:
// with them form.name, form.title, form.submit, … are these controls, but nothing in the app
// reads, calls or writes those properties there — react, react-dom and scheduler 18.3.1 never
// access title, method, submit, reset, lang, dir, role, hidden, head, elements or cookie at all,
// and read name, id, action, target and location only on other objects (functions, inputs,
// props, events, hook updates, the window, whose location no element can shadow), body only on
// the document; VTS code reads no property of a form. The fix of runtime-r2-3 rejected every
// property name of a form and of the document (attack-1 r1: name="name", "title", "location").
// The window shows a control by its id only, so a name may be a global the bundle reads (jest).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

export function Signup() {
  const [sent, setSent] = useState<int>(0);
  invariant(sent >= 0);
  return (
    <form
      name="name"
      onSubmit={(e) => {
        e.preventDefault();
        setSent(sent + 1);
      }}
    >
      <input name="name" id="title" />
      <input name="title" />
      <input name="location" />
      <input name="id" />
      <input name="action" />
      <input name="method" />
      <input name="target" />
      <textarea name="body" />
      <select name="lang" id="dir">
        <option value="en">en</option>
      </select>
      <input name="role" />
      <input name="hidden" />
      <input name="head" />
      <input name="elements" />
      <input name="cookie" />
      <input name="jest" />
      <button type="reset" name="reset">reset</button>
      <button type="submit" name="submit">send ({sent})</button>
    </form>
  );
}
