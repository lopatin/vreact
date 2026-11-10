// expect: verified Viewer=verified Notes=verified Page=verified Toggle=verified Levels=verified Opt=verified
// Keyed siblings with distinct keys verify: distinct written keys; the reset idiom on two
// siblings with different literal prefixes; an int key next to a key that is no number;
// equal keys on children that are never present together; keys of different arrays (a keyed
// list and a fragment are arrays of their own, and so are the children of another element); an
// undefined key, which is no key.
import { useState } from "react";
import { distinct, invariant, type int } from "vreact/spec";
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
      <Viewer key={`viewer-${props.doc}`} doc={props.doc} />
      <Notes key={`notes-${props.doc}`} doc={props.doc} />
      <p key="title">title</p>
      <p key={props.doc}>{props.doc}</p>
      <p key="footer">footer</p>
    </div>
  );
}
export function Toggle() {
  const [on, setOn] = useState<boolean>(false);
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <button onClick={() => setOn(!on)}>toggle</button>
      {on && <p key="a">on</p>}
      {!on && <p key="a">off</p>}
      {on ? <b key="x">x</b> : <i key="x">x</i>}
      <p key={`n${n}`}>{n}</p>
      <p key={`m${n + 1}`}>{n}</p>
      <button key={n} onClick={() => setN(n + 1)}>{n}</button>
      <button key={n + 1} onClick={() => setN(n + 1)}>{n}</button>
    </div>
  );
}
export function Levels() {
  const [xs, setXs] = useState<readonly string[]>(["head", "a"]);
  invariant(distinct(xs));
  return (
    <ul>
      <li key="head">head</li>
      {xs.map((x) => (
        <li key={x}>
          <span key="head">{x}</span>
          <span key="tail">{x}</span>
        </li>
      ))}
      <>
        <li key="head">again</li>
      </>
      <li key="tail">
        <button onClick={() => setXs([])}>clear</button>
      </li>
    </ul>
  );
}
export function Opt(props: { readonly k?: int }) {
  return (
    <div>
      <p key={props.k}>k</p>
      <p key="undefined">title</p>
    </div>
  );
}
