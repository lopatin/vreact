// expect: reject `+` converts the number `n` to a string with JS's Number::toString
// number + string: JS's shortest round-trip formatting of a double is not modelled.
export function f(n: number): string {
  return "n = " + n;
}
