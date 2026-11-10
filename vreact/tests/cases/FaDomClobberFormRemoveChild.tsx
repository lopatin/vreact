// expect: reject name="removeChild" on <input>
// The click deletes <p>: react-dom's commit calls form.removeChild(p), which is the <input>
// (named access), and throws a TypeError. VERIFIED before.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Del() {
  const [c, setC] = useState<int>(0);
  invariant(c >= 0 && c <= 1);
  return (
    <form>
      <input name="removeChild" />
      {c === 0 && <p>zero</p>}
      <button type="button" onClick={() => setC(1)}>go</button>
    </form>
  );
}
