// Runtime half of vreact/spec. Contracts are erased (no-ops) unless checking is enabled.
// `vreact synth` runs candidates in test mode: requires() rejects inputs, ensures() records postconditions.
let checking = false;
export function setContractChecking(on) { checking = !!on; }
function check(kind, cond) { if (checking && !cond) throw new Error(`vreact: ${kind} violated`); }
const T = () => globalThis.__VREACT_TEST__;
export class PreconditionFailed extends Error {}
export function requires(cond) {
  const t = T();
  if (t && !cond) throw new PreconditionFailed("precondition");
  check("precondition", cond);
}
export function ensures(post) { const t = T(); if (t) t.posts.push(post); }
export function invariant(cond) { check("invariant", cond); }
export function callbackRequires(_cb, _pre) {}
export function assert(cond) { const t = T(); if (t && !cond) throw new Error("assertion failed"); check("assertion", cond); }
export function assume(_cond) {}
export function decreases(_m) {}
export function forall(lo, hi, p) { for (let i = lo; i < hi; i++) if (!p(i)) return false; return true; }
export function exists(lo, hi, p) { for (let i = lo; i < hi; i++) if (p(i)) return true; return false; }
export function distinct(xs, key = (x) => x) { return new Set(xs.map(key)).size === xs.length; }
export function implies(a, b) { return !a || b; }
export function idiv(a, b) { if (b === 0) throw new Error("idiv by zero"); return Math.floor(a / b); }
export function range(n) { return Array.from({ length: Math.max(0, n) }, (_, i) => i); }
export function hole() { const t = T(); if (t && t.fill) return t.fill(); throw new Error("vreact: unfilled hole() — run `vreact synth`"); }
