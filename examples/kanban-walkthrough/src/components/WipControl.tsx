import { requires, callbackRequires, type int } from "vreact/spec";

type WipControlProps = { readonly limit: int; readonly inProgress: int; readonly onChange: (limit: int) => void };

/** Adjusts the WIP limit; never proposes a limit below the work already in progress. */
export function WipControl(props: WipControlProps) {
  requires(props.limit >= 1 && props.inProgress <= props.limit);
  callbackRequires(props.onChange, (n) => n >= 1 && n >= props.inProgress);
  const canLower = props.limit - 1 >= 1 && props.limit - 1 >= props.inProgress;
  return (
    <div className="wip">
      WIP limit{" "}
      <button disabled={!canLower} onClick={() => { if (canLower) props.onChange(props.limit - 1); }}>−</button>
      <b>{props.limit}</b>
      <button onClick={() => props.onChange(props.limit + 1)}>+</button>
    </div>
  );
}
