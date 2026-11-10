// expect: reject name="_wrapperState" on <textarea>
// React keeps state on DOM nodes under names starting with "_" (_valueTracker, _wrapperState,
// __reactFiber$…, __reactProps$…, __reactEvents$…): a control so named on a form is what React
// reads there, and defining such a property on the form throws. Every name starting with "_" is
// rejected on form controls.
export function Note() {
  return (
    <form>
      <textarea name="_wrapperState" defaultValue="" />
    </form>
  );
}
