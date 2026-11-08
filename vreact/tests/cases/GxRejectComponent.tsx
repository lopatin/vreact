// expect: reject generic components are not supported in VTS
// A generic component: React renders it with no type arguments; its props must be concrete.
import { ensures, requires, type int } from "vreact/spec";

export function List<T>(props: { readonly n: int; readonly first: T }) {
  return <p>{props.n}</p>;
}
