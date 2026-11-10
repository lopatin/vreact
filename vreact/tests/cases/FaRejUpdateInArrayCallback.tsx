// expect: reject not inside a callback that VTS translates as a value, such as an array method's
// A setter inside an array callback in an effect: rejected, and the message says why (it is
// not "during render", and moving it "into an event handler or effect" cannot help: it is in one).
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";
export function B() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    console.log([-5].map((x) => { setN(x); return x; }));
  });
  return <p>{n}</p>;
}
