// expect: verified
// A callback with an obligation of its own (`xs[sel]`) inside a handler: the handler's
// obligation sees the callback itself, not an unassigned metavariable (elaboration order:
// the field access `x.v` on the callback's element postponed the callback).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

type It = { readonly id: int; readonly v: int };

export function TrAttachIdx() {
  const [xs] = useState<readonly It[]>([{ id: 1, v: 1 }]);
  const [ys, setYs] = useState<readonly It[]>([]);
  const [zs, setZs] = useState<readonly int[]>([]);
  const [sel, setSel] = useState<int>(0);
  invariant(xs.every((x) => x.v >= 1) && ys.every((y) => y.v >= 2) && zs.every((z) => z >= 2));
  return (
    <div>
      <button onClick={() => {
        if (sel < 0 || sel >= xs.length) return;
        const rest = xs.filter((x) => x.v > xs[sel].v);
        setYs(rest);
      }}>{ys.length}</button>
      <button onClick={() => {
        if (sel < 0 || sel >= xs.length) return;
        setZs(xs.map((x) => x.v + xs[sel].v));
      }}>{zs.length}</button>
      <button onClick={() => setSel(sel + 1)}>next</button>
    </div>
  );
}
