// expect: reject is=… makes a customized built-in element
// Sibling of the custom-element rejection: `is` creates a customized built-in element
// (document.createElement("button", { is: "x-btn" })), whose behaviour script outside the
// verified program defines.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjIsAttr() {
  const [n, setN] = useState<int>(0);
  return <button is="x-btn" type="button" onClick={() => setN(n + 1)}>{n}</button>;
}
