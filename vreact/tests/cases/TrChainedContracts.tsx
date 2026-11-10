// expect: verified
// Several requires(…) / invariant(…) of a component form one condition each, in order:
// a later one may rely on the earlier ones as guards (as with `&&`, and as in functions).
import { useState } from "react";
import { requires, invariant, type int } from "vreact/spec";

export function TrHead(props: { readonly xs: readonly int[] }) {
  requires(props.xs.length > 0);
  requires(props.xs[0] >= 0);
  const [i, setI] = useState<readonly int[]>([1]);
  invariant(i.length > 0);
  invariant(i[0] >= 1);
  return (
    <button onClick={() => setI([i.length + 1])}>
      {props.xs[0]} {i[0]}
    </button>
  );
}

export function TrHeadParent() {
  return <TrHead xs={[3, 4]} />;
}
