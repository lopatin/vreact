// expect: reject effect cleanups may not use the function `setN` here other than by calling it
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// [1].map(setN) calls the setter during the cleanup (not translated): the state becomes 1
export function PassSetter(props: { readonly k: int }) {
  const [n, setN] = useState<int>(0);
  invariant(n === 0);
  useEffect(() => {
    return () => {
      console.log([1].map(setN));
    };
  }, [props.k]);
  return <p>{n}</p>;
}
