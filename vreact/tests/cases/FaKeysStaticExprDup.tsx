// expect: fail unique-keys Page=incomplete Same=incomplete Orphan=incomplete Viewer=verified Notes=verified faildesc=keys~of~the~children~of~<div>~are~distinct
// Keys given by expressions on sibling elements must be provably distinct as strings: the
// key-to-reset idiom applied to two siblings (effects-r1-1), `key={n}` next to `key={n * 1}`
// (jsx-r1-3), and two buttons keyed by the same state, whose stale copy React would leave in
// the DOM and let a click break lo <= hi (skeptic jsx-r1-3-2).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Viewer(props: { readonly doc: int }) {
  return <h1>doc {props.doc}</h1>;
}
export function Notes(props: { readonly doc: int }) {
  const [draft, setDraft] = useState<string>("");
  return <input value={draft} onChange={(e) => setDraft(e.currentTarget.value)} />;
}
export function Page(props: { readonly doc: int }) {
  return (
    <div>
      <Viewer key={props.doc} doc={props.doc} />
      <Notes key={props.doc} doc={props.doc} />
    </div>
  );
}
export function Same() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>+</button>
      <p key={n}>three</p>
      <p key={n * 1}>four</p>
    </div>
  );
}
export function Orphan() {
  const [lo, setLo] = useState<int>(0);
  const [hi, setHi] = useState<int>(10);
  invariant(0 <= lo && lo <= hi);
  return (
    <div>
      <button type="button" key={hi} onClick={() => setLo(hi)}>raise</button>
      <button type="button" key={hi} onClick={() => { if (hi > lo) setHi(hi - 1); }}>lower</button>
    </div>
  );
}
