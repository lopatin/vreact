// expect: verified
// Concatenation of string literals is a literal (`"a" + "b" === "ab"`), also in template literals
// with literal parts, after `String(…)`/`${…}` of an int or boolean literal, and re-associated
// (`s + "a" + "b" === s + "ab"`).
import { requires, ensures, type int } from "vreact/spec";

export function hello(): string {
  ensures((r: string) => r === "Hello, world");
  return "Hello, " + "world";
}

export function tmpl(): string {
  ensures((r: string) => r === "id-7");
  return `id-${"7"}`;
}

export function concat3(): boolean {
  ensures((r: boolean) => r);
  return "a" + "b" + "c" === "abc";
}

export function differ(): boolean {
  ensures((r: boolean) => !r);
  return "a" + "b" === "ba";
}

export function tmplNum(): string {
  ensures((r: string) => r === "n=7");
  return `n=${7}`;
}

export function tmplNeg(): string {
  ensures((r: string) => r === "-12px");
  return `${-12}px`;
}

export function tmplBool(): string {
  ensures((r: string) => r === "on:true");
  return `on:${true}`;
}

export function strNum(): string {
  ensures((r: string) => r.length === 3);
  return String(120);
}

export function assoc(s: string): boolean {
  ensures((r: boolean) => r);
  return s + "a" + "b" === s + "ab";
}

export function wrap(n: string): string {
  ensures((r: string) => r === "<" + n + ">");
  return `<${n}>`;
}

export function lenLit(s: string): int {
  requires(s.length === 4);
  ensures((r: int) => r === 9);
  return ("x-" + s + "-y" + "!").length;
}
