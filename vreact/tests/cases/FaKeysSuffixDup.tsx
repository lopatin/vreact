// expect: fail unique-keys SameEnd=incomplete EndOfLit=incomplete IntDigit=incomplete faildesc=keys~of~the~children~of~<div>~are~distinct
// Keys with literal ends that can still be equal fail: two ids with the same suffix (equal ids),
// an id with a suffix next to a literal that ends with it (the id "x"), an int with a digit
// appended next to a literal of digits (n = 1 gives "11").
import { type int } from "vreact/spec";
export function SameEnd(props: { readonly a: string; readonly b: string }) {
  return (
    <div>
      <p key={`${props.a}-x`}>a</p>
      <p key={`${props.b}-x`}>b</p>
    </div>
  );
}
export function EndOfLit(props: { readonly a: string }) {
  return (
    <div>
      <p key={`${props.a}-title`}>a</p>
      <p key="x-title">b</p>
    </div>
  );
}
export function IntDigit(props: { readonly n: int }) {
  return (
    <div>
      <p key={`${props.n}1`}>a</p>
      <p key="11">b</p>
    </div>
  );
}
