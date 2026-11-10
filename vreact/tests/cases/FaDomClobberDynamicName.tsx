// expect: reject VTS cannot tell what this one may be
// The name comes from what the user types: typing parentNode makes form.parentNode this input.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Named() {
  const [name, setName] = useState<string>("");
  const [c, setC] = useState<int>(0);
  invariant(c >= 0 && c <= 1);
  return (
    <form>
      <input value={name} onChange={(e) => setName(e.target.value)} />
      <input name={name} />
      <input type="radio" name="size" checked={c === 0} onChange={() => setC(0)} />
      <input type="radio" name="size" checked={c === 1} onChange={() => setC(1)} />
    </form>
  );
}
