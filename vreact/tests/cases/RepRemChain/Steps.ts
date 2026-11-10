// expect: fail postcondition failtext=timeout faildesc=postcondition~of~step verdict=not-verified mix=verified walk=verified
// A chain of 12 nested `%`: once `mix` is unfolded, the contract instances of the remainders
// repeat each argument, so the goal's terms, as trees, have about 3^12 nodes, though they share
// their parts. The automation's own walks over the goal (the calls that get contract instances,
// counts, index terms, `Nodup` facts; the sizes of the cases after a timeout) visit each distinct
// subterm once: the obligation runs out of its budget of 100000 heartbeats in seconds (the case
// takes about 10 s). Before, they walked the trees, which allocates almost nothing and so
// advances no heartbeats: this case did not finish in 12 minutes (with 7 remainders, the walks
// of one run of the automation's preparation took about 40 s).
import { ensures, implies, type int } from "vreact/spec";

type Feed = { readonly offset: int; readonly seed: int };
type A = { readonly kind: "walk" } | { readonly kind: "bump" } | { readonly kind: "stay" };

export function mix(s: int): int {
  const x0 = s;
  const x1 = (x0 * 75 + 74) % 65537;
  const x2 = (x1 * 75 + 74) % 65537;
  const x3 = (x2 * 75 + 74) % 65537;
  const x4 = (x3 * 75 + 74) % 65537;
  const x5 = (x4 * 75 + 74) % 65537;
  const x6 = (x5 * 75 + 74) % 65537;
  const x7 = (x6 * 75 + 74) % 65537;
  const x8 = (x7 * 75 + 74) % 65537;
  const x9 = (x8 * 75 + 74) % 65537;
  const x10 = (x9 * 75 + 74) % 65537;
  const x11 = (x10 * 75 + 74) % 65537;
  const x12 = (x11 * 75 + 74) % 65537;
  return x12;
}

export function walk(f: Feed): Feed {
  const seed = mix(f.seed);
  const move = (seed % 5) - 2;
  const next = f.offset + move;
  return { offset: next > 40 || next < -40 ? f.offset - move : next, seed: seed };
}

export function step(f: Feed, paused: boolean, a: A): Feed {
  ensures((r: Feed) => implies(paused, r.offset === f.offset && r.seed === f.seed));
  switch (a.kind) {
    case "walk":
      return walk(f);
    case "bump":
      return f.offset >= 40 ? f : { ...f, offset: f.offset + 1 };
    case "stay":
      return f;
  }
}
