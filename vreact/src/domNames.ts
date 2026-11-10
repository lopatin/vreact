/**
 * Names that HTML's named access must not give to an element (`vreact verify` rejects them as the
 * `name` or `id` of the elements below; component.ts, `checkNamedAccess`).
 *
 * A form's named getter (HTMLFormElement is [LegacyOverrideBuiltIns]) answers `form.x` with the
 * control or image whose name or id is "x" before any property of the form, so `form.parentNode`
 * is `<input name="parentNode">`, and react-dom 18.3.1, which walks `parentNode` up from a radio
 * button (updateNamedCousins), loops forever; `<input name="removeChild">` makes React's commit
 * throw. Document's named getter does the same with the names of `<img>`, `<form>`, `<embed>`,
 * `<iframe>` and `<object>` and the ids of `<object>` and of an `<img>` with a name:
 * `<img name="createElement">` breaks every element React creates later. Window's named
 * properties shadow only names the window does not define (no [LegacyOverrideBuiltIns]), with any
 * element's id.
 *
 * So the reserved names are those of every property of a form and of the document — the own
 * property names along the prototype chains of a `<form>` and of `document` in Chromium 152, the
 * members TypeScript 5.6's lib.dom.d.ts gives HTMLFormElement and Document (with what they
 * inherit) and Firefox's non-standard ones — together with `RESERVED_PATTERN` (event handler
 * attributes `on…`, vendor-prefixed and ARIA reflection names, and every name starting with `_`:
 * React's expandos on DOM nodes `__reactFiber$…`, `_valueTracker`, `_wrapperState`, …), and the
 * names react-dom 18.3.1 reads on a node that may be a form or the document although no browser
 * defines them there (`REACT_READS`). react-dom reads nothing else by name on such a node: its
 * other property reads are on fibers, events, its own objects, or nodes it has picked by tag
 * (an `<input>`'s `value`, a `<select>`'s `options`), which have no named getter.
 */

/** react-dom 18.3.1 reads these on an event target, the focused element or the document, which may be a form or the document (`getEventTarget`, `getEventTargetDocument`, EnterLeaveEventPlugin, the fallback composition state, IE's input polyfill, hydration's comment check), and, with the `window` fallback node of ChangeEventPlugin and SelectEventPlugin, on the window */
const REACT_READS = ["correspondingUseElement", "parentWindow", "window", "document", "documentMode", "attachEvent", "detachEvent", "value", "type", "data", "checked", "nodeName", "contentEditable"];

/** Event handler attributes, vendor-prefixed names, ARIA reflection, and `_…` (React's expandos, `__proto__`, `__defineGetter__`, …). */
export const RESERVED_PATTERN = /^(?:_|on[a-z]|aria[A-Z]|(?:webkit|WebKit|Webkit|moz|Moz|ms|MS)[A-Z])/;

const PROTO_NAMES = [
  "ATTRIBUTE_NODE CDATA_SECTION_NODE COMMENT_NODE DOCUMENT_FRAGMENT_NODE DOCUMENT_NODE",
  "DOCUMENT_POSITION_CONTAINED_BY DOCUMENT_POSITION_CONTAINS DOCUMENT_POSITION_DISCONNECTED",
  "DOCUMENT_POSITION_FOLLOWING DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC",
  "DOCUMENT_POSITION_PRECEDING DOCUMENT_TYPE_NODE ELEMENT_NODE ENTITY_NODE ENTITY_REFERENCE_NODE",
  "NOTATION_NODE PROCESSING_INSTRUCTION_NODE TEXT_NODE URL acceptCharset accessKey accessKeyLabel",
  "action activeElement activeViewTransition addEventListener adoptNode adoptedStyleSheets after",
  "alinkColor all anchors animate append appendChild applets assignedSlot attachInternals",
  "attachShadow attributeStyleMap attributes autocapitalize autocomplete autofocus baseURI before",
  "bgColor blockedNodeByClassifierCount blockedNodesByClassifier blur body browsingTopics",
  "captureEvents caretPositionFromPoint caretRangeFromPoint characterSet charset checkValidity",
  "checkVisibility childElementCount childNodes children classList className clear click",
  "clientHeight clientLeft clientTop clientWidth cloneNode close closest compareDocumentPosition",
  "compatMode completeStorageAccessRequestFromSite computedStyleMap constructor contains",
  "contentEditable contentType convertPointFromNode convertQuadFromNode convertRectFromNode cookie",
  "createAttribute createAttributeNS createCDATASection createComment createDocumentFragment",
  "createElement createElementNS createEvent createExpression createNSResolver createNodeIterator",
  "createProcessingInstruction createRange createTextNode createTreeWalker currentCSSZoom",
  "currentScript customElementRegistry dataset defaultView designMode dir dispatchEvent doctype",
  "documentElement documentURI domain draggable editContext elementFromPoint elementTiming",
  "elements elementsFromPoint embeds enableStyleSheetsForSet encoding enctype enterKeyHint",
  "evaluate execCommand exitFullscreen exitPictureInPicture exitPointerLock featurePolicy fgColor",
  "firstChild firstElementChild focus focusGroup focusGroupStart fonts forms fragmentDirective",
  "fullscreen fullscreenElement fullscreenEnabled getAnimations getAttribute getAttributeNS",
  "getAttributeNames getAttributeNode getAttributeNodeNS getBoundingClientRect getBoxQuads",
  "getClientRects getElementById getElementsByClassName getElementsByName getElementsByTagName",
  "getElementsByTagNameNS getHTML getRootNode getSelection hasAttribute hasAttributeNS",
  "hasAttributes hasChildNodes hasFocus hasOwnProperty hasPointerCapture hasPrivateToken",
  "hasRedemptionRecord hasStorageAccess hasUnpartitionedCookieAccess head hidden hidePopover id",
  "images implementation importNode inert innerHTML innerText inputEncoding inputMode",
  "insertAdjacentElement insertAdjacentHTML insertAdjacentText insertBefore isConnected",
  "isContentEditable isDefaultNamespace isEqualNode isPrototypeOf isSameNode lang lastChild",
  "lastElementChild lastModified lastStyleSheetSet length linkColor links localName location",
  "lookupNamespaceURI lookupPrefix matches method moveBefore name namespaceURI nextElementSibling",
  "nextSibling noValidate nodeName nodeType nodeValue nonce normalize offsetHeight offsetLeft",
  "offsetParent offsetTop offsetWidth open outerHTML outerText ownerDocument parentElement",
  "parentNode part pictureInPictureElement pictureInPictureEnabled plugins pointerLockElement",
  "popover preferredStyleSheetSet prefix prepend prerendering previousElementSibling",
  "previousSibling propertyIsEnumerable pseudo queryCommandEnabled queryCommandIndeterm",
  "queryCommandState queryCommandSupported queryCommandValue querySelector querySelectorAll",
  "readyState referrer rel relList releaseCapture releaseEvents releasePointerCapture remove",
  "removeAttribute removeAttributeNS removeAttributeNode removeChild removeEventListener",
  "replaceChild replaceChildren replaceWith reportValidity requestFullscreen requestPointerLock",
  "requestStorageAccess requestStorageAccessFor requestStorageAccessUnderSite requestSubmit reset",
  "role rootElement scripts scroll scrollBy scrollHeight scrollIntoView scrollIntoViewIfNeeded",
  "scrollLeft scrollLeftMax scrollTo scrollTop scrollTopMax scrollWidth scrollingElement",
  "selectedStyleSheetSet setAttribute setAttributeNS setAttributeNode setAttributeNodeNS",
  "setCapture setHTML setHTMLUnsafe setPointerCapture shadowRoot showPopover slot spellcheck",
  "startViewTransition style styleSheetSets styleSheets submit tabIndex tagName target textContent",
  "timeline title toLocaleString toString toggleAttribute togglePopover translate valueOf",
  "virtualKeyboardPolicy visibilityState vlinkColor wasDiscarded when write writeln",
  "writingSuggestions xmlEncoding xmlStandalone xmlVersion",
].join(" ").split(" ");

/** Names a form control (or an image) of a form, or an element the document's named getter exposes, may not have. */
export const RESERVED_NAMES: ReadonlySet<string> = new Set([...PROTO_NAMES, ...REACT_READS]);

/**
 * Names no element's id may be (the window's named properties): the global names the app bundle
 * reads at run time that the window does not define — react-dom's `window` fallback node
 * (`window.nodeName.toLowerCase()` in ChangeEventPlugin throws when an element has the id
 * "nodeName"), the development build's test-environment flags, and `RESERVED_PATTERN`'s `_…`
 * (`__REACT_DEVTOOLS_GLOBAL_HOOK__`, the test hook of a vreact/spec runtime before 2026-11).
 */
export const WINDOW_RESERVED: ReadonlySet<string> = new Set(["nodeName", "contentEditable", "type", "correspondingUseElement", "IS_REACT_ACT_ENVIRONMENT", "jest", "MSApp"]);

export function reservedName(s: string): boolean {
  return RESERVED_NAMES.has(s) || RESERVED_PATTERN.test(s);
}

export function windowReserved(s: string): boolean {
  return WINDOW_RESERVED.has(s) || s.startsWith("_");
}
