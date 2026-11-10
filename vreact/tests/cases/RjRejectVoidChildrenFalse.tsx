// expect: reject <input> is a void element: React throws while rendering it with children
// Even `{false}`, which renders nothing, is a child: React checks `children != null`.
import { useState } from "react";

export function RjVoidChildrenFalse() {
  const [s, setS] = useState<string>("");
  return <input value={s} onChange={(e) => setS(e.currentTarget.value)}>{false}</input>;
}
