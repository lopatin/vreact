// expect: reject import cycle
// Components of two modules that render each other: the modules import each other, and
// vreact rejects the import cycle (the render cycle is never translated).
import { type int } from "vreact/spec";
import { B } from "./B";
export function A(props: { readonly d: int }) {
  return <div>{props.d > 0 ? <B d={props.d - 1} /> : null}</div>;
}
