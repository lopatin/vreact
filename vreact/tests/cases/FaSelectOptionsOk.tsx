// expect: verified
// Accepted counterparts of FaSelect*: a <select> holding <option>s and <optgroup>s, written
// directly, in a keyed list, under a condition or as a JSX const; options whose label is text
// (strings, numbers, conditionals); e.target.value in a select's onChange (its content makes no
// onChange, so the target is the select), e.currentTarget.value in its onInput; a <datalist> of
// options for a text field; an option's own handler.
import { useState } from "react";
import { type int, distinct, invariant, requires } from "vreact/spec";

export function FaSelectOptionsOk(props: { opts: readonly string[] }) {
  requires(distinct(props.opts) && props.opts.every((o) => o !== "none"));
  const [s, setS] = useState<string>("none");
  const [n, setN] = useState<int>(0);
  invariant(s.length >= 0 && n >= 0);
  const none = <option value="none">none ({n})</option>;
  return (
    <div>
      <select value={s} onChange={(e) => setS(e.target.value)}>
        {none}
        <optgroup label="picks">
          {props.opts.map((o) => <option key={o} value={o}>{o}</option>)}
        </optgroup>
        {n > 0 ? <option value="many">{n} picks</option> : null}
        <option value="x" disabled>{"x"}</option>
      </select>
      <select value={s} onInput={(e) => setS(e.currentTarget.value)}>
        <option value="a">a</option>
        <option value="b" onClick={() => setN(n + 1)}>b</option>
      </select>
      <input list="names" value={s} onChange={(e) => setS(e.target.value)} />
      <datalist id="names">
        <option value="ann" />
        <option value="bob">Bob</option>
      </datalist>
    </div>
  );
}
