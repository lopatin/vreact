// expect: reject mutates the array
import { useState } from "react";
export function Bad() {
  const [xs, setXs] = useState<readonly number[]>([]);
  return <button onClick={() => { const ys = [...xs]; ys.push(1); setXs(ys); }}>add</button>;
}
