// expect: reject value on an <input> that may be type="file"
// A type computed from a string may be "file" (or "FILE": HTML matches it ASCII-case-
// insensitively), and React then sets the file input's value: an InvalidStateError.
import { useState } from "react";

export function RjFileValueDynamic() {
  const [t, setT] = useState<string>("text");
  const [s, setS] = useState<string>("");
  return (
    <div>
      <input value={t} onChange={(e) => setT(e.currentTarget.value)} />
      <input type={t} value={s} onChange={(e) => setS(e.currentTarget.value)} />
    </div>
  );
}
