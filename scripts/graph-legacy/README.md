# Frozen development comparator

These files are the unmodified browser renderer from repository commit
`c7e3781cb5bc1b630b9c63f4d468bed3a344f48b`. They are retained for the old-engine
tests and explicit development comparisons. They are outside both public
assets and the packaged renderer's files. No production caller imports them.

The frozen full-output capture at the start of the migration includes the
renderer’s post-layout port choices, shortcuts, smoothing and crossing casings.
Comparisons must use that complete output, not only this layout module's ranks.
