// expect: reject a Map or Set has no indexed elements
import { useState } from "react";
import { type int } from "vreact/spec";

// clears the parent's Map prop (no cast needed: the prop is typed Map)
export function C(props: { readonly m: Map<int, int> }) {
  const [n, setN] = useState<int>(0);
  return (
    <button
      onClick={() => {
        console.log(props.m["clear"]());
        setN(props.m.size);
      }}
    >
      {n}
    </button>
  );
}
