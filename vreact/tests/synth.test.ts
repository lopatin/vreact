/** Synthesis regression: fill three holes of a cart model and check the programs found. */
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { synthCommand } from "../src/synth.ts";

const here = path.dirname(fileURLToPath(import.meta.url));
const dir = path.join(here, ".work", "synth");
fs.rmSync(dir, { recursive: true, force: true });
fs.mkdirSync(path.join(dir, "src"), { recursive: true });
fs.copyFileSync(path.join(here, "todo", "tsconfig.json"), path.join(dir, "tsconfig.json"));
fs.copyFileSync(path.join(here, "synth", "cart.holes.ts"), path.join(dir, "src", "cart.ts"));
const res = await synthCommand(dir, ["src/cart.ts"], { write: true });
const expect: Record<string, RegExp> = {
  addItem: /\[\.\.\.c\.items, \{ id: c\.nextId, qty: 1 \}\].*nextId: c\.nextId \+ 1/,
  removeItem: /c\.items\.filter\(\(x\) => x\.id !== id\)/,
  bump: /c\.items\.map\(\(x\) => \(x\.id === id \? \{ \.\.\.x, qty: x\.qty \+ 1 \} : x\)\)/,
};
let ok = true;
for (const r of res) {
  const pass = !!r.solution && r.proved && expect[r.fn]?.test(r.solution);
  ok &&= !!pass;
  console.log(`${pass ? "✓" : "✗"} ${r.fn}: ${r.solution ?? "(none)"}`);
}
console.log(ok ? "✔ synthesis regression passed" : "✗ synthesis regression failed");
process.exit(ok ? 0 : 1);
