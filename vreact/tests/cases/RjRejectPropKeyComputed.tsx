// expect: reject a prop named key: React uses key={…}
// A prop type field written with a computed name ["key"] (or an escape, k\u0065y) is the prop
// `key`, which React never passes to the component: the names are the properties' own, not
// their source text.
import { type int } from "vreact/spec";

type BProps = { ["key"]: int; n: int };

export function RjKeyChild(props: BProps) {
  return <p>{props.key + props.n}</p>;
}

export function RjKeyParent() {
  return <RjKeyChild key={3} n={1} />;
}
