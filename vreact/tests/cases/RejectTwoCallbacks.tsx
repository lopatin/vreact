// expect: reject at most one parent callback
type Props = { readonly onA: () => void; readonly onB: () => void };
export function Bad(props: Props) {
  return <button onClick={() => { props.onA(); props.onB(); }}>both</button>;
}
