// expect: verified verdict=verified inc=verified errors=none
// A proof file with CRLF line endings that imports another proof file (attack on the fix of
// report-r1-3): Lean reads CRLF as LF, so proofs/m.lean imports Proofs.lemmas.H and lake builds
// it; vreact's line regex did not match `import Proofs.lemmas.H\r` and rejected H as imported by
// nothing ("Lean would never check it"; before that fix, the kernel re-check replayed m before H:
// "unknown constant helper_ok"). m_ok uses H's lemma, so the run verifies only if H is imported.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
