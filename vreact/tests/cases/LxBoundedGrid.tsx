// expect: verified TicTacToe=verified Nine=verified
// P56 / V8: bounded quantifiers a realistic board needs: a 2-D grid (an instance that is itself a
// guarded quantifier), 9 cells (above the old enumeration cap of 8), a two-sided body
// (`cells[i] >= 0 && cells[i] <= 2`, a guard the second conjunct does not use) kept by `.with`.
/// <reference lib="es2023.array" />
import { useState } from "react";
import { requires, ensures, invariant, forall, range, type int } from "vreact/spec";

export function corner(g: readonly (readonly int[])[]): int {
  requires(g.length === 2 && forall(0, 2, (r) => g[r].length === 2 && forall(0, 2, (c) => g[r][c] >= 0)));
  ensures((v: int) => v >= 0);
  return g[1][1];
}
export function nine(): readonly int[] {
  ensures((r: readonly int[]) => r.length === 9 && forall(0, 9, (i) => r[i] >= 0 && r[i] <= 2));
  return [0, 0, 0, 0, 0, 0, 0, 0, 0];
}
export function step(cells: readonly int[], k: int): readonly int[] {
  requires(cells.length === 9 && forall(0, 9, (i) => cells[i] >= 0 && cells[i] <= 2) && 0 <= k && k < 9);
  ensures((r: readonly int[]) => r.length === 9 && forall(0, 9, (i) => r[i] >= 0 && r[i] <= 2));
  return cells.with(k, 1);
}

export function TicTacToe() {
  const [cells, setCells] = useState<readonly int[]>([0, 0, 0, 0, 0, 0, 0, 0, 0]);
  const [turn, setTurn] = useState<int>(1);
  invariant(cells.length === 9 && forall(0, 9, (i) => cells[i] >= 0 && cells[i] <= 2));
  invariant(turn === 1 || turn === 2);
  return (
    <div>
      {range(9).map((k) => (
        <button key={k} onClick={() => { if (cells[k] === 0) { setCells(cells.with(k, turn)); setTurn(3 - turn); } }}>{cells[k]}</button>
      ))}
      <button onClick={() => setCells([0, 0, 0, 0, 0, 0, 0, 0, 0])}>reset</button>
    </div>
  );
}
export function Nine() {
  const [cells, setCells] = useState<readonly int[]>([0, 0, 0, 0, 0, 0, 0, 0, 0]);
  invariant(cells.length === 9 && forall(0, 9, (i) => cells[i] >= 0));
  return (
    <div>
      {range(9).map((k) => <button key={k} onClick={() => setCells(cells.with(k, cells[k] + 1))}>{cells[k]}</button>)}
    </div>
  );
}
