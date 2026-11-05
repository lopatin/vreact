// expect: reject state updates during render
import { useState } from "react";
export function Bad() {
  const [n, setN] = useState(0);
  setN(1);
  return <p>{n}</p>;
}
