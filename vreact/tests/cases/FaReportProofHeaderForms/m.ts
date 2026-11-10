// expect: verified verdict=verified inc=verified errors=none
// Header forms Lean accepts, read as Lean reads them (the positive side of
// FaReportProofHiddenImport): comments (nested, line) before and between the imports, two imports
// on one line, an import whose name is on the next line, an escaped name component. vreact
// rejects a proof file whose imports it reads otherwise than Lean; here both readings agree and
// m_ok needs the lemmas of A, B and C, so the run verifies only if all three are imported.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
