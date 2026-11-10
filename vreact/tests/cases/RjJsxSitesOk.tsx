// expect: verified
// Accepted counterparts of the JSX rejections of round 2: a value on an <input> whose type is a
// choice between strings or an enum without "file" (a password toggle); "" on a file input;
// void elements without children; an upper-case type keyword (HTML matches it ASCII-case-
// insensitively); handlers on SVG elements; HTML controls inside <foreignObject>, whose children
// are HTML again; a JSX const of SVG elements, rendered inside <svg> (its namespace is that of
// where it is rendered); record fields named by strings ("b", ["c"]) are the properties b and c.
import { useState } from "react";
import { invariant, ensures, type int } from "vreact/spec";

type Kind = "text" | "password";
type R = { readonly a: int; readonly "b": int; readonly ["c"]: int };

export function sum(r: R): int {
  ensures((x: int) => x === r.a + r.b + r.c);
  const { "c": z } = r;
  return r.a + r.b + z;
}

export function six(): int {
  ensures((x: int) => x === 6);
  return sum({ a: 1, "b": 2, ["c"]: 3 });
}

export function RjJsxSitesOk() {
  const [s, setS] = useState<string>("");
  const [show, setShow] = useState(false);
  const [k, setK] = useState<Kind>("text");
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const grad = <linearGradient id="g"><stop offset="0" /></linearGradient>;
  return (
    <div>
      <input type={show ? "text" : "password"} value={s} onChange={(e) => setS(e.currentTarget.value)} />
      <input type={k} value={s} onInput={(e) => setS(e.currentTarget.value)} />
      <input type="file" value="" onChange={() => setN(n + 1)} />
      <input type="CheckBox" checked={show} onChange={(e) => setShow(e.currentTarget.checked)} />
      <button type="button" onClick={() => setK(k === "text" ? "password" : "text")}>toggle</button>
      <svg width="10" height="10">
        <defs>{grad}</defs>
        <rect width="5" height="5" onClick={() => setN(n + 1)} />
        <foreignObject width="10" height="10">
          <textarea value={s} onChange={(e) => setS(e.currentTarget.value)} />
        </foreignObject>
      </svg>
      <hr />
      <br></br>
      <img alt="x" src="data:," />
      <input type="TEXT" onKeyDown={(e) => setS(e.key)} />
      <p>{s.length}</p>
    </div>
  );
}
