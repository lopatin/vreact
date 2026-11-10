// expect: reject name="body" on <form>: HTML's named access makes this element the property body of the document
// The document shows a <form> by its name; react-dom reads document.body (getActiveElement:
// `doc.activeElement || doc.body`), so body is reserved there, although a form control may have
// it (FaDomNamesCommon: a form's body is read by nothing).
export function Note() {
  return (
    <form name="body">
      <textarea name="body" defaultValue="" />
    </form>
  );
}
