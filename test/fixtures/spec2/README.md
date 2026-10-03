# A spec-2 database record

`lax-38/` is one record of `lax-database` in the shape a spec-2 record
stores (`recorded-shape.ts` in the `lax` repository, and
`spike/axiomfree/build-output-investigation-20261003.md` there): the
manifest carries no `id`, each proof stores its telescope and no
`conclusion` or `assumptions`, the capture lists no files and no pins but
carries `bytes`, `fileCount` and its `references` layer, and the
`certificate` block holds `Challenge.lean` verbatim. The digests are
placeholders; `test/spec2.test.ts` overrides the `references` layer with a
tar it seals itself before exercising the download path.

The second proof assumes the same statement twice, once implicitly: the
telescope keeps both, in binder order, and the derived `assumptions` set
has one entry — the one case where the two shapes differ visibly.
