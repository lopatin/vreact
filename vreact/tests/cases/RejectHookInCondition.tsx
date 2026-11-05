// expect: reject Rules of Hooks
import { useState } from "react";
export function Bad(props: { readonly on: boolean }) {
  if (props.on) {
    const [n] = useState(0);
    return <p>{n}</p>;
  }
  return <p>off</p>;
}
