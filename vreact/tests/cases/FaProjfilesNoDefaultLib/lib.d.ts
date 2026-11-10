/// <reference no-default-lib="true"/>
/// <reference lib="es2023" />
/// <reference lib="dom" />
interface ReadonlyArray<T> {
  find(predicate: (value: T) => boolean): T | null;
}
