# Browser integration evidence

`test/graph-browser.test.ts` generates a four-submission diagnostic site with
the pinned archive measurement host, then loads the resulting static HTML in
the selected browser engine. These are integration fixtures, not the real
archive benchmark corpus or a browser performance measurement.

The archive host remains Chrome for Testing **150.0.7871.124** in every run.
Firefox and WebKit consume its published SVG and measured text coordinates;
they do not choose a different public layout. The extracted-renderer test also
exercises the separately packaged local measurement helper and worker using
the selected runtime browser's exact text metrics.

## Reproduction

The suite runs when `GRAPH_CHROME` supplies the archive measurement executable.
Without an explicit browser configuration it is skipped, so an ordinary local
renderer installation does not acquire a browser download. Setting
`GRAPH_BROWSER=firefox` or `GRAPH_BROWSER=webkit` explicitly requests that
engine; a missing measurement host, runtime executable, or system dependency
then fails the suite. `GRAPH_BROWSER_EXECUTABLE` can supply an explicit runtime
path. Runtime versions are checked against the installed Playwright package's
`browsers.json`; the default Chromium runtime is checked against the archive
measurement pin.

Provision the optional development browsers from the lockfile-installed
Playwright CLI, without installing system packages:

```sh
PLAYWRIGHT_BROWSERS_PATH=/tmp/lax-graph-playwright \
  node node_modules/playwright-core/cli.js install firefox webkit
```

The recorded runs used Playwright Core **1.62.1** and Ubuntu **22.04.5 LTS**,
x86-64. The browser assets are its Ubuntu 22.04 builds. Neither these browsers
nor Playwright are transferred to site visitors or required by the packaged
local renderer.

```sh
GRAPH_CHROME=/tmp/lax-graph-chrome/chrome-linux64/chrome \
  npm run check -- graph-browser

PLAYWRIGHT_BROWSERS_PATH=/tmp/lax-graph-playwright \
  GRAPH_BROWSER=firefox \
  GRAPH_CHROME=/tmp/lax-graph-chrome/chrome-linux64/chrome \
  npm run check -- graph-browser

PLAYWRIGHT_BROWSERS_PATH=/tmp/lax-graph-playwright \
  GRAPH_BROWSER=webkit \
  GRAPH_BROWSER_EXECUTABLE=/tmp/lax-graph-playwright-libs/webkit-headless.sh \
  GRAPH_CHROME=/tmp/lax-graph-chrome/chrome-linux64/chrome \
  npm run check -- graph-browser
```

Set `GRAPH_SCREENSHOTS=/absolute/output/directory` on a run to retain the tested
visual states as PNGs plus `manifest-<engine>.json`. Capture is off by default.
The manifest records the runtime and measurement browser versions, viewport
dimensions, state names and layout digests. Screenshots cover the default and
JavaScript-disabled proof network, all-ancestry view, zoom/fullscreen/resize,
normal/expanded math tooltips, a narrow reduced-motion screen, and the local
worker result. This output directory is separate from disposable test sites
and must stay out of Git. It supplements the real-corpus gallery rather than
replacing it.

## Covered behavior

All engines run the same nine cases:

1. JavaScript-disabled graphs contain visible SVG and real navigable anchors,
   including distinct proof incidences and numbered statement docks.
2. All four ancestry/descendant states switch correctly, including three
   lazily fetched alternate views and a direct skip import. Relative links
   and static geometry URLs remain within a nested preview prefix.
3. Fullscreen, resize, zoom and keyboard controls preserve the SVG element,
   node positions, edge paths, attachments and layout digest. The initial
   viewport is at the top and horizontally centered.
4. Hover and focus highlight incident edges and show the white inspector:
   proof descriptions/title math, concept/status/submission fields, or
   submission/content/state/relation fields. Normal inspectors sit outside
   the graph at the node's vertical center; expanded views use an opaque
   white panel nearby. Only field names are bold. SVG accessibility names do
   not trigger native tooltips. Every graph has one matching control banner
   above its viewport, including ancestry controls where applicable. Panning
   clips at the window rather than at the original SVG drawing bounds.
   Scrollbars are selected independently for each axis from the current zoom
   and window size, rather than the SVG's unchanged intrinsic dimensions.
5. Delayed font requests do not change reserved graph dimensions or geometry.
   Once fonts load, independently read SVG text bounds fit their containing
   node bodies and numbered docks. The visible labels remain 12px in the
   declared font stack.
6. A 390px-wide viewport with reduced motion and touch retains usable graph
   controls and an on-screen tooltip. Firefox uses narrow desktop viewport
   and touch emulation because Playwright does not implement its mobile
   context emulation.
7. A self-contained `file:` export switches views without fetching geometry.
   Anonymous graph payloads and hover panels exclude the fixture's author
   and source repository metadata.
8. An actual npm tarball is extracted outside the repository. Only declared
   production dependencies are exposed to that host, where importing
   Playwright is confirmed to fail. The generated local page measures its
   labels, runs the first-party worker, receives all three complete validated
   SVGs, and enables the same controls. Worker module transfers include the
   independent validator and exclude the Node-dependent measurement and
   projection modules.
9. An independent display fixture emits a multiline label and a large dock
   ordinal (`9876543210`) through the production SVG serializer. With page
   JavaScript disabled, actual glyph bounds fit the unchanged node and dock
   rectangles, and every line retains its measured baseline and fixed
   statement attachment. The pinned Chromium runtime also reproduces the
   measured ink bounds; Firefox and WebKit retain the published coordinates
   and independently pass ink containment.

The suite observes CSP violations and uncaught page errors. Public views must
make no calls to the legacy layout entry point, start no workers, perform no
SVG text measurement, and transfer no layout engine. Account and comment
service requests are stubbed; this evidence does not test those external
services. Server-side request observation verifies actual worker module
transfers because Firefox's Playwright request events omit some worker imports.

Exact serialized geometry comparisons use no tolerance. After fullscreen,
viewport height comparisons allow less than 0.01 CSS px to accommodate
Firefox's observed `715.9999694824219` versus `716` subpixel result. Text
containment allows 0.02 SVG units for bounding-box numeric representation;
no label is shrunk or moved to satisfy the check. The new ordinal fixture
checks containment without that margin, and its pinned-host ink comparison
allows less than 0.005 SVG units for numeric representation.

## Host dependency provenance

The host was missing `libavif.so.13`, required by the downloaded WebKit build,
and two of its transitive dependencies, `libgav1.so.0` and `libyuv.so.0`.
The official Ubuntu Jammy package index supplied the following amd64 artifacts;
each downloaded SHA-256 matched that metadata before extraction.

| Package / version | Bytes | SHA-256 |
| --- | ---: | --- |
| [libavif13 0.9.3-3](https://archive.ubuntu.com/ubuntu/pool/universe/liba/libavif/libavif13_0.9.3-3_amd64.deb) | 69,454 | `c7b6af0c598ed4a7cad6ded2e759205014359bc67b5b08031c94e0ec22749f43` |
| [libgav1-0 0.17.0-1build1](https://archive.ubuntu.com/ubuntu/pool/universe/libg/libgav1/libgav1-0_0.17.0-1build1_amd64.deb) | 335,742 | `000319b8be18170aa1cc7c3c61c163a851f57fbf3ef4308776b656e968ebe928` |
| [libyuv0 0.0~git20220104.b91df1a-2](https://archive.ubuntu.com/ubuntu/pool/universe/liby/libyuv/libyuv0_0.0~git20220104.b91df1a-2_amd64.deb) | 154,248 | `db4c34e67ab9d2f745f5f1934bc23f7db5d0a1d31910cf58f9695a3078a997b7` |

`dpkg-deb --extract` placed its files under `/tmp/lax-graph-playwright-libs`.
No system package installation or package-manager state change occurred.
The bundled WebKit launcher replaces `LD_LIBRARY_PATH`, so a temporary launcher
sets the same WebKit bundle paths and adds the isolated dependency directory:

```sh
#!/bin/sh
set -eu
lax_graph_webkit_dir=/tmp/lax-graph-playwright/webkit-2336/minibrowser-wpe
export WEBKIT_EXEC_PATH="$lax_graph_webkit_dir/bin"
export WEBKIT_INJECTED_BUNDLE_PATH="$lax_graph_webkit_dir/lib"
export WEBKIT_INSPECTOR_RESOURCES_PATH="$lax_graph_webkit_dir/share"
export WEBKIT_FORCE_COMPLEX_TEXT=1
export LD_LIBRARY_PATH="/tmp/lax-graph-playwright-libs/usr/lib/x86_64-linux-gnu:$lax_graph_webkit_dir/lib:$lax_graph_webkit_dir/sys/lib"
exec "$lax_graph_webkit_dir/bin/MiniBrowser" "$@"
```

This script is `/tmp/lax-graph-playwright-libs/webkit-headless.sh`, mode 755.
Only the selected WebKit runtime receives its `LD_LIBRARY_PATH` addition.
These temporary libraries are absent from normal builds, the renderer tarball and public
site assets.

## Recorded results

Recorded on 13 September 2026. Earlier WebKit attempts failed at host setup
until the missing libraries and bundle launcher path were resolved; those
attempts did not execute the assertions and are not counted as passing runs.

| Runtime engine | Exact version / Playwright build | Result |
| --- | --- | --- |
| Chromium | Chrome for Testing 150.0.7871.124 | 9 / 9 passed in the full repository check |
| Firefox | 153.0 / 1538 | 9 / 9 passed; suite duration 21.22 s |
| WebKit | 26.5 / 2336 | 9 / 9 passed; suite duration 31.80 s |

The full repository check passed all 351 tests in 40 files in 24.61 s. These
suite durations include test setup and are not graph interaction performance
measurements. The final screenshot artifacts are in
`/tmp/lax-graph-browser-evidence-20260913-final`, outside Git.

The new ink case initially timed out in Firefox, both alongside WebKit and
when run alone: returning `document.fonts.ready` from automation in a page
with JavaScript disabled did not settle. The test now polls the synchronous
`document.fonts.status` from the host until it is `loaded`. All nine Firefox
cases then passed with the same geometry, ink and attachment assertions.
This correction changes only the test's readiness wait.

These results cover the tested Linux builds and fixture tier. A Playwright
WebKit run is engine-level evidence, not a claim of testing Safari on macOS or
iOS. It does not establish full-corpus screenshot equivalence or mobile
performance targets.
