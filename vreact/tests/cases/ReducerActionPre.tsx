// expect: status tally=verified Stepper=verified Counter=verified
// A reducer's requires about the action alone is proved at each dispatch site — from a
// constant, from the snapshot + invariant + branch condition, from a child's
// callbackRequires, and in a timer — never checked at run time. The reducer's own
// ensures needs it (n >= 1), and the timer makes the handlers rebase-checked: the action
// is fixed at dispatch, so its precondition survives React applying it to a newer state.
import { useEffect, useReducer } from "react";
import { requires, ensures, implies, invariant, callbackRequires, type int } from "vreact/spec";

type Tally = { readonly total: int };
type Action = { readonly kind: "add"; readonly n: int } | { readonly kind: "reset" };

export function validAction(a: Action): boolean {
  return a.kind === "add" ? 1 <= a.n && a.n <= 10 : true;
}

export function tally(s: Tally, a: Action): Tally {
  requires(validAction(a));
  ensures((r: Tally) => implies(s.total >= 0, r.total > 0 || a.kind === "reset"));
  switch (a.kind) {
    case "add":
      return { total: s.total + a.n };
    case "reset":
      return { total: 0 };
  }
}

type StepperProps = { readonly onStep: (n: int) => void };

export function Stepper(props: StepperProps) {
  callbackRequires(props.onStep, (n) => 1 <= n && n <= 10);
  return <button onClick={() => props.onStep(3)}>+3</button>;
}

export function Counter() {
  const [s, dispatch] = useReducer(tally, { total: 0 });
  invariant(s.total >= 0);
  useEffect(() => {
    const id = setInterval(() => dispatch({ kind: "add", n: 1 }), 1000);
    return () => clearInterval(id);
  }, []);
  return (
    <div>
      <p>{s.total}</p>
      <button onClick={() => dispatch({ kind: "add", n: 1 })}>+1</button>
      <button onClick={() => dispatch({ kind: "reset" })}>reset</button>
      <button
        onClick={() => {
          if (s.total < 10) dispatch({ kind: "add", n: 10 - s.total });
        }}
      >
        fill to 10
      </button>
      <Stepper onStep={(n) => dispatch({ kind: "add", n: n })} />
    </div>
  );
}
