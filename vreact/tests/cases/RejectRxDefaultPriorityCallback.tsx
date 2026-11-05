// expect: reject parent callbacks cannot be invoked
// A default-priority event (animationend) may run with a stale snapshot: it may
// not call parent callbacks.
type Props = { readonly onDone: () => void };
export function Banner(props: Props) {
  return <div onAnimationEnd={() => props.onDone()}>hello</div>;
}
