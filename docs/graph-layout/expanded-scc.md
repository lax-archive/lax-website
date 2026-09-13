# Expanded displayed cycles

`layoutGroups(graph, layoutDag, inputDigest, profile)` lays out actual display
SCCs and returns complete `GraphGeometry`. The callback supplies an ordinary
validated DAG layout; the module imports no second layout engine. Root
orchestration splits weak components before this operation and translates the
complete geometry, including gates, when packing components.

Every SCC with more than one member, or a singleton with a self-loop, receives
a containing envelope. The group is a presentation object. Its member nodes,
proof incidence nodes, numbered ports and semantic edges remain present with
their original IDs. A display cycle is not labeled a circular proof or a
kernel failure. The initial group has an accessible description and no
unmeasured visible label.

The conservative interior places members in a row. Each incidence owns a
different lane above and below the complete row envelope, plus a separate
vertical column in an empty well beside the row. North/south ports reach their
lane directly. East/west ports escape through separately reserved columns in
the gaps beside their own measured box. Two ports in the same hemisphere use
one outer horizontal lane; opposite hemispheres connect through the incidence's
reserved vertical column. All semantic arrow directions remain unchanged,
including feedback routes and self-loops.

These channels make obstacle avoidance inspectable: horizontal runs lie outside
the row envelope, row-crossing columns lie outside every member envelope, and
terminal stubs use their owner's side or its reserved side gap. Different
incidences have different lane heights and transit columns. Actual edge
crossings are retained and reported by the independent validator; overlapping
runs and contacts with arrowhead exclusions invalidate a candidate. Tight or
coincident fixed incidence attachments are diagnosed, rather than shifted to
different numbered docks.

For every external incidence, a fixed north (outgoing) or south (incoming)
boundary gate is added to the condensation supernode. Each gate records its
original edge ID. Interior adapters end exactly at the gate; the outer DAG's
route begins there, or conversely for incoming edges. The final output replaces
the supernode with its actual members and records the containing envelope in
`geometry.groups`. Layout gates are in `group.gates`, not in the semantic
`geometry.ports` list. Complete route-section chains preserve each original
edge, and only the final section carries the original target's arrow marker.

The full graph is rebuilt at envelope scales 1, 2 and 3 if validation fails.
This is a fixed operation schedule. Members are never moved after routes have
been selected, and failed attempts never publish a collapsed or partial
replacement. Persistent failures produce `scc-layout-invalid` with the final
independent diagnostics. Every returned candidate has been quantized,
serialized through the SVG path language, parsed back, and independently
validated.

The frozen initial corpus has no genuine display SCC. Synthetic tests in
`test/graph-groups.test.ts` therefore exercise internal and external edges,
two connected SCCs, self-loops, proof incidence cycles created by display
grouping, fixed statement attachments, east/west ports, deterministic input
reordering, component packing translations, unordered callback section arrays,
24 dense/parallel incidence fixtures, and bounded failure diagnostics.
This fallback prioritizes traceability and complete semantic coverage. Its
generous dimensions are not evidence of a compact or optimized SCC drawing.
