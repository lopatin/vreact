// expect: reject unary + converts a string to a number
// `+s` is ToNumber(s) (a number, NaN for "abc"), not the string itself.
export function incremented(s: string): string {
  const n = +s;
  return `${n + 1}`;
}
