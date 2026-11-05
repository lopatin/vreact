// expect: status verdict=verified-modulo-trusted absT=trusted viaT=relative guess=assumes viaGuess=assumes Badge=trusted Plain=verified UsesGuess=assumes UsesT=relative WithBadge=relative Plain.certificate=verified UsesGuess.certificate=assumes UsesT.certificate=relative WithBadge.certificate=relative errors=none
// Statuses follow the dependency cone (the axioms Lean reports for each item): a component
// or certificate that uses a function that uses an assume() is ASSUMES, one that uses a
// @trusted function or renders a @trusted component is VERIFIED* (relative), never VERIFIED;
// the verdict is "VERIFIED modulo …", not VERIFIED.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
import { viaGuess, viaT } from "./model";
type BadgeProps = { readonly v: int };
/** @trusted */
export function Badge(props: BadgeProps) {
  return <b>{props.v}</b>;
}
export function Plain() {
  return <p>hi</p>;
}
export function UsesGuess() {
  return <p>{viaGuess([1, 2])}</p>;
}
export function UsesT() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(viaT(n))}>{n}</button>;
}
export function WithBadge() {
  return (
    <div>
      <Badge v={1} />
    </div>
  );
}
