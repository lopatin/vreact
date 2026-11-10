// expect: reject id="appendChild" on <select>
// A control's id names it on its form like its name does: on mount react-dom appends <p> to the
// (new) form with form.appendChild, which is the <select>. VERIFIED before.
export function Mount() {
  return (
    <form>
      <select id="appendChild">
        <option value="a">a</option>
      </select>
      <p>hi</p>
    </form>
  );
}
