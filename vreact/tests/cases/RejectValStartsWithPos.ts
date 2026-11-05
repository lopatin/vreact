// expect: reject a position is not supported
// "ab".startsWith("a", 1) is false: the position argument must not be dropped.
export function startsAt1(s: string): boolean {
  return s.startsWith("a", 1);
}
