// expect: reject compares object identity
import { useState } from "react";
type P = { readonly x: number };
export function Bad() {
  const [a] = useState<P>({ x: 1 });
  const [b] = useState<P>({ x: 1 });
  return <p>{a === b ? "same" : "different"}</p>;
}
