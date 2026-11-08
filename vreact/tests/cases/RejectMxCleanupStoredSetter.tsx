// expect: reject effect cleanups may not use the function `setN` here other than by calling it
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// a setter stored as the toString of an object literal: String(…) calls it (with no argument)
// during the cleanup, which is not translated
export function StoredToString(props: { readonly k: int }) {
  const [n, setN] = useState<int>(0);
  invariant(n === 0);
  useEffect(() => {
    return () => {
      console.log(String({ toString: setN }));
    };
  }, [props.k]);
  return <p>{n}</p>;
}
