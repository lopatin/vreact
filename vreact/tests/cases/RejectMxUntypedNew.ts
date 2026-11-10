// expect: reject TypeScript types this
import { type int } from "vreact/spec";

// TypeScript types new Map() Map<any, any>: it checks nothing about the entries
export function f(): int {
  const m = new Map();
  return m.size;
}
