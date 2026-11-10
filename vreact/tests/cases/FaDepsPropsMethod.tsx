// expect: reject `props.m.has` is a method, not a dependency
// The props branch of the dependency check: `props.m.has` does not change with props.m.
import { useMemo } from "react";
import { type int } from "vreact/spec";

type P = { readonly m: ReadonlyMap<int, string> };
export function FaDepsPropsMethod(props: P) {
  const label: string = useMemo(() => (props.m.has(2) ? "two" : "none"), [props.m.has]);
  return <p>{label}</p>;
}
