// expect: fail effect-robust Stale=incomplete After=incomplete Weak=incomplete Functional=incomplete
// Timer path conditions are about the effect's snapshot, never the current state, and
// only those before the registration count: each timer below can break its invariant.
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Stale() {
  const [n, setN] = useState<int>(0);
  const [m] = useState<int>(5);
  invariant(n <= m);
  useEffect(() => {
    if (n >= m) return;
    const id = setTimeout(() => setN(n + 1), 10);
    return () => clearTimeout(id);
  }, [n, m]);
  return <p>{n}</p>;
}
export function After() {
  const [left, setLeft] = useState<int>(10);
  invariant(left >= 0);
  useEffect(() => {
    const id = setTimeout(() => setLeft(left - 1), 1000);
    if (left <= 0) return;
    return () => clearTimeout(id);
  }, [left]);
  return <p>{left}</p>;
}
export function Weak() {
  const [left, setLeft] = useState<int>(10);
  invariant(left >= 0);
  useEffect(() => {
    if (left < 0) return;
    const id = setTimeout(() => setLeft(left - 1), 1000);
    return () => clearTimeout(id);
  }, [left]);
  return <p>{left}</p>;
}
export function Functional() {
  const [left, setLeft] = useState<int>(10);
  invariant(left >= 0);
  useEffect(() => {
    if (left <= 0) return;
    const id = setTimeout(() => setLeft((l) => l - 1), 1000);
    return () => clearTimeout(id);
  }, [left]);
  return <p>{left}</p>;
}
