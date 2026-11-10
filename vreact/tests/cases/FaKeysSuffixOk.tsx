// expect: verified Suffix=verified IntSuffix=verified Title=verified Ends=verified IntEnd=verified Rows=verified
// Keys that differ only at their end verify (they verified before keyed siblings had a
// unique-keys obligation): one id with two suffixes, an id and the id with a suffix, an id with a
// suffix next to the suffix alone, different ids with suffixes whose last characters differ, an
// int (whose decimal form ends with a digit) next to a key that ends with a letter.
import { useState } from "react";
import { type int } from "vreact/spec";
export function Suffix(props: { readonly id: string }) {
  return (
    <div>
      <p key={`${props.id}-title`}>x</p>
      <p key={`${props.id}-body`}>y</p>
    </div>
  );
}
export function IntSuffix(props: { readonly id: int }) {
  return (
    <div>
      <p key={props.id}>a</p>
      <p key={`${props.id}-edit`}>b</p>
    </div>
  );
}
export function Title(props: { readonly id: string }) {
  return (
    <div>
      <h2 key="title">t</h2>
      <p key={`${props.id}-title`}>x</p>
      <p key={`item-${props.id}-title-x`}>y</p>
    </div>
  );
}
export function Ends(props: { readonly from: string; readonly to: string }) {
  return (
    <div>
      <p key={`${props.from}-from`}>a</p>
      <p key={`${props.to}-to`}>b</p>
    </div>
  );
}
export function IntEnd(props: { readonly n: int; readonly s: string }) {
  return (
    <div>
      <p key={props.n}>n</p>
      <p key={`${props.s}-edit`}>s</p>
    </div>
  );
}
export function Rows() {
  const [sel, setSel] = useState<int>(0);
  return (
    <ul>
      <li key={sel} onClick={() => setSel(sel + 1)}>{sel}</li>
      <li key={`${sel}-detail`}>detail</li>
      {sel > 2 && <li key={`${sel}-more`}>more</li>}
    </ul>
  );
}
