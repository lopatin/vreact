// expect: reject is the effect's return value, which React calls as its cleanup
// An arrow's expression body is its return value: this effect returns what `show()`
// returns — the assigned title (a `() => void` type does not make it undefined) — which
// React keeps as the cleanup and calls on unmount (TypeError: destroy is not a function).
// (TypeScript itself rejects a timer id or an assignment there.)
import { useEffect } from "react";
export function RjEffectReturnsId(props: { readonly title: string }) {
  const show: () => void = () => (document.title = props.title);
  useEffect(() => show());
  return <p>{props.title}</p>;
}
