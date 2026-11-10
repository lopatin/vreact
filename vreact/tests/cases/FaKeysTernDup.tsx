// expect: fail unique-keys Tern=incomplete Page=incomplete Editor=verified Viewer=verified Notes=verified faildesc=keys~of~the~children~of~<div>~are~distinct
// The branches of `c ? a : b` put their keyed elements into the parent's children array: while
// c holds, Tern's first child has the key "a", like its sibling (written as an expression, so
// this is an obligation, not a rejection); while edit holds, Page's Editor has the key of the
// Notes next to it (the reset idiom on a branch and a sibling).
import { useState } from "react";
import { type int } from "vreact/spec";
export function Tern(props: { readonly c: boolean }) {
  return (
    <div>
      {props.c ? <p key="a">x</p> : <p key="b">y</p>}
      <p key={"a" as const}>z</p>
    </div>
  );
}
export function Editor(props: { readonly doc: int }) {
  const [draft, setDraft] = useState<string>("");
  return <input value={draft} onChange={(e) => setDraft(e.currentTarget.value)} />;
}
export function Viewer(props: { readonly doc: int }) {
  return <h1>doc {props.doc}</h1>;
}
export function Notes(props: { readonly doc: int }) {
  return <p>notes {props.doc}</p>;
}
export function Page(props: { readonly doc: int; readonly edit: boolean }) {
  return (
    <div>
      {props.edit ? <Editor key={props.doc} doc={props.doc} /> : <Viewer key={`v${props.doc}`} doc={props.doc} />}
      <Notes key={props.doc} doc={props.doc} />
    </div>
  );
}
