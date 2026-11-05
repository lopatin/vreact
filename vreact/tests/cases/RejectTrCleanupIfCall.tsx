// expect: reject effect cleanups may not call `Date.now` here
// The condition of an if in a cleanup must be pure, too.
import { useEffect } from "react";
export function TrCleanupCond() {
  useEffect(() => {
    const id = setTimeout(() => console.log("t"), 10);
    return () => {
      if (Date.now() > 0) clearTimeout(id);
    };
  }, []);
  return <p>x</p>;
}
