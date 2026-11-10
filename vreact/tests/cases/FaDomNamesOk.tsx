// expect: verified Fields=verified
// Names and ids that are no property of a form or the document, or values that cannot be one
// (a string with a literal part holding a character outside [A-Za-z0-9_$]; a choice between such
// literals; an enum), are accepted on form controls, images, forms and objects; on
// other elements only the window sees an id, and only global names the app reads are reserved
// there (a computed id is not checked).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

type Size = "small" | "large";

export function Fields() {
  const [n, setN] = useState<int>(0);
  const [size, setSize] = useState<Size>("small");
  const [label, setLabel] = useState<string>("");
  invariant(n >= 0);
  return (
    <form name="signup">
      <label htmlFor="email">e-mail</label>
      <input id="email" name="email" type="email" />
      <input type="radio" name="size" checked={size === "small"} onChange={() => setSize("small")} />
      <input type="radio" name={size} checked={size === "large"} onChange={() => setSize("large")} />
      <input id={"qty-" + n} name={`qty-${n}`} type="number" />
      <select name={n === 0 ? "first" : "later"} id={`sel-${n}`}>
        <option value="a">a</option>
      </select>
      <img id="logo-img" src="logo.png" alt="logo" />
      <iframe name="preview" title="preview" />
      <input name="" />
      <h2 id="title">{label}</h2>
      <p id={label}>{n}</p>
      <input value={label} onChange={(e) => setLabel(e.target.value)} />
      <button type="button" onClick={() => setN(n + 1)}>more</button>
    </form>
  );
}
