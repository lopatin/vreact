// expect: verified
// Lone surrogates are exact code units: one unit each, distinct from U+FFFD.
import { ensures } from "vreact/spec";

export function loneLen(): boolean {
  ensures((r: boolean) => r === true);
  return "\uD83D".length === 1 && `${"\uDE00"}`.length === 1;
}

export function pair(): boolean {
  ensures((r: boolean) => r === true);
  return ("\uD83D" + "\uDE00").length === "😀".length;
}

export function notReplacement(): boolean {
  ensures((r: boolean) => r === false);
  const lone: string = "\uD83D";
  return lone === "�";
}
