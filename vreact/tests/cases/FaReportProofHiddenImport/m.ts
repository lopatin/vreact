// expect: reject proofs/Orphan.lean:1:1: no generated module imports the proof file proofs/Orphan.lean ;; proofs/OrphanCR.lean:1:1: no generated module imports the proof file proofs/OrphanCR.lean ;; proofs/OrphanLS.lean:1:1: no generated module imports the proof file proofs/OrphanLS.lean
// The import graph of the proof files is read as Lean reads the headers (attack on the fix of
// report-r1-3). In proofs/m.lean every `import` is inside a comment for Lean: block comments
// nest, so the first `-/` does not end the outer one; a line comment ends only at a line feed,
// not at a lone CR or a U+2028. vreact's regexes read all three imports, so it took Orphan,
// OrphanCR and OrphanLS (a false `decide` theorem and a `sorry` each) for imported, lake never
// built them, and the run said VERIFIED, exit 0. Nothing imports them: rejected.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
