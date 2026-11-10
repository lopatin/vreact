// expect: verified
// Accepted counterparts of RjRejectEventBivariant*: an event field is read where the element
// and the handler prop make it a string (a boolean): the value of an <input>, <select>,
// <textarea> or <button> it is on (e.currentTarget), e.target where nothing inside the element
// can be the target (an <input>, a <textarea>, a <select>'s onChange), an <input>'s checked,
// a keyboard event's key; also through a handler passed by name and an annotated parameter.
import { useState, type ChangeEvent } from "react";
import { invariant } from "vreact/spec";

export function RjEventSitesOk() {
  const [s, setS] = useState<string>("");
  const [on, setOn] = useState<boolean>(false);
  invariant(s.length >= 0);
  const onText = (e: ChangeEvent<HTMLInputElement>) => setS(e.target.value);
  return (
    <div>
      <input value={s} onChange={onText} />
      <input value={s} onChange={(e: ChangeEvent<HTMLInputElement>) => setS(e.currentTarget.value)} />
      <select value={s} onChange={(e) => setS(e.target.value)}>
        <option value="a">a</option>
        <option value="b">b</option>
      </select>
      <textarea value={s} onChange={(e) => setS(e.target.value)} />
      <textarea value={s} onInput={(e) => setS(e.currentTarget.value)} />
      <input type="checkbox" checked={on} onChange={(e) => setOn(e.target.checked)} />
      <button type="button" value="b" onClick={(e) => setS(e.currentTarget.value)}>b</button>
      <p tabIndex={0} onKeyDown={(e) => setS(e.key)}>{on ? s : ""}</p>
    </div>
  );
}
