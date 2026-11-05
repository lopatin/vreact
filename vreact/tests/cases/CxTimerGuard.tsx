// expect: status Countdown=verified Capped=verified Assumed=assumes Asserted=verified Narrowed=verified Ticker=verified
// A timer is registered only past the effect body's top-level early returns
// (`if (c) return;`), asserts and assumes, which are about the snapshot the timer
// captures: its callback is checked under them (the common guarded countdown).
import { useEffect, useState } from "react";
import { assert, assume, invariant, type int } from "vreact/spec";
export function Countdown() {
  const [left, setLeft] = useState<int>(10);
  invariant(left >= 0);
  useEffect(() => {
    if (left <= 0) return;
    const id = setTimeout(() => setLeft(left - 1), 1000);
    return () => clearTimeout(id);
  }, [left]);
  return <p>{left}</p>;
}
export function Capped() {
  const [n, setN] = useState<int>(0);
  invariant(n <= 5);
  useEffect(() => {
    if (n > 3) return;
    const id = setTimeout(() => { assert(n + 1 <= 4); setN(n + 1); }, 10);
    return () => clearTimeout(id);
  }, [n]);
  return <p>{n}</p>;
}
export function Assumed() {
  const [n, setN] = useState<int>(0);
  invariant(n <= 4);
  useEffect(() => {
    assume(n <= 3);
    const id = setTimeout(() => setN(n + 1), 10);
    return () => clearTimeout(id);
  }, [n]);
  return <p>{n}</p>;
}
export function Asserted() {
  const [n, setN] = useState<int>(0);
  invariant(n <= 3);
  useEffect(() => {
    if (n >= 3) {
      return;
    }
    assert(n + 1 <= 3);
    const id = setTimeout(() => setN(n + 1), 10);
    return () => clearTimeout(id);
  }, [n]);
  return <p>{n}</p>;
}
type Item = { readonly count: int };
export function Narrowed(props: { readonly item: Item | null }) {
  const [x, setX] = useState<int>(0);
  invariant(x >= 0);
  const item = props.item;
  useEffect(() => {
    if (item === null) return;
    if (item.count < 0) return;
    const id = setTimeout(() => setX(item.count), 10);
    return () => clearTimeout(id);
  }, [item]);
  return <p>{x}</p>;
}
export function Ticker() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 5);
  useEffect(() => {
    if (n >= 5) return;
    const id = setInterval(() => setN(n + 1), 100);
    return () => clearInterval(id);
  }, [n]);
  return <p>{n}</p>;
}
