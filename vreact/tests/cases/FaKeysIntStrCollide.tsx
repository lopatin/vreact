// expect: fail unique-keys IntStr=incomplete Templ=incomplete NullKey=incomplete
// React turns every key into a string ('' + key): key={1} and key="1" are one key, and so are
// key={k} and key={`${k}`} (lean-r1-1 dynamic keys); a null key is the key "null" (React 18's
// jsx() ignores only an undefined key).
import { useState } from "react";
import { type int } from "vreact/spec";
export function IntStr() {
  const [k, setK] = useState<int>(2);
  return (
    <div>
      <button onClick={() => setK(k + 1)}>next</button>
      <p key={1}>c</p>
      <p key="1">d</p>
    </div>
  );
}
export function Templ() {
  const [k, setK] = useState<int>(1);
  return (
    <div>
      <button onClick={() => setK(k + 1)}>next</button>
      <p key={k}>a</p>
      <p key={`${k}`}>b</p>
    </div>
  );
}
export function NullKey(props: { readonly j: int | null }) {
  return (
    <div>
      <p key={props.j}>j</p>
      <p key="null">n</p>
    </div>
  );
}
