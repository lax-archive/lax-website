import { attr } from "./graph-escape.js";

/** Shared by archive SVG, packaged local rendering, and graph legends.
 * Keep the existing marker scale and clearance envelope; narrow its profile. */
export function graphArrowMarker(id: string): string {
  return `<marker id="${attr(id)}" viewBox="0 -5 10 10" refX="8.5" refY="0" markerWidth="7" markerHeight="7" markerUnits="userSpaceOnUse" orient="auto" overflow="visible"><path fill="context-stroke" stroke="none" d="M0.8,-3.1 L8.5,0 L0.8,3.1 Q2.8,0 0.8,-3.1 Z"/></marker>`;
}
