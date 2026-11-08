// expect: reject truthiness of a value of the type parameter K is not supported
// filter tests its callback's result for truthiness; K extends boolean is still abstract (and
// TypeScript types `x` by the constraint there).
export function trues<K extends boolean>(xs: readonly K[]): readonly K[] {
  return xs.filter((x) => x);
}
