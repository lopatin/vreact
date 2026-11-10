// expect: reject an optional field named `__defineSetter__` is not supported
// The same in a component's props: `<Show />` passes no such prop, and `props.__defineSetter__`
// reads Object.prototype's function.
import { type int } from "vreact/spec";

export function Show(props: { readonly __defineSetter__?: int }) {
  return <p>{props.__defineSetter__ === undefined ? "none" : "some"}</p>;
}

export function RnProtoOptionalProp() {
  return <Show />;
}
