// expect: reject missing dependencies: step
import { useState, useEffect } from "react";
export function Bad() {
  const [n, setN] = useState(0);
  const [step] = useState(1);
  useEffect(() => { setN((m) => m + step); }, []);
  return <p>{n}</p>;
}
