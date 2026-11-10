// expect: verified FaDepsEffectOutsideImport=verified
// An imported function or constant (a top-level declaration of another module: an import binding
// cannot be reassigned, and top-level variables are const) never changes: as an effect dependency,
// directly or through a useCallback, it contributes no dependency value. Before, `[clampUp]` was
// refused with "functions are not first-class in VTS; call the function instead".
import { useState, useCallback, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
import { clampUp, STEP as S } from "./lib";

export function FaDepsEffectOutsideImport() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const bump = useCallback(() => setN((p) => clampUp(p, S)), [clampUp, S]);
  useEffect(() => {
    bump();
  }, [bump]);
  useEffect(() => {
    setN((p) => clampUp(p, 1));
  }, [clampUp]);
  return <p>{n}</p>;
}
