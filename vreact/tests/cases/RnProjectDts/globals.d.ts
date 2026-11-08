export {};
declare global {
  interface ReadonlyArray<T> {
    head(): T;
  }
}
