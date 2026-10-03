/** Data contract consumed from the public lax-db repository. */

export interface Author {
  name: string;
  orcid?: string;
  github?: string;
}

export interface Manifest {
  /** The content spec the record follows: `"1"` (statements are `axiom`s,
   * proofs are checked by the archive's pipeline) or `"2"` (statements are
   * tagged `Prop` definitions, proofs are telescopes over them, and the record
   * carries a comparator certificate). A spec-2 record stores no `id` in its
   * manifest; the loader fills it from the record's own id. */
  specVersion: string;
  id: string;
  leanVersion: string;
  mathlibVersion: string;
  title: string;
  authors: Author[];
  bibEntries: string[];
  /** Omit this submission from discovery surfaces while keeping its pages addressable. */
  unlisted?: boolean;
  /** Suppress authorship and source links on presentation surfaces. */
  anonymous?: boolean;
  /** The submission this one replaces; binding once this one is registered. */
  supersedes?: string;
  /** The declared paper, when the manifest carries one. A spec-2 record's
   * `paper` block reads `folder`, `main`, and `engine` from here. */
  paper?: { folder: string; main: string; engine: string; [key: string]: unknown };
}

export interface SourceTriple {
  repository: string;
  commit: string;
  folder: string;
}

/**
 * A database record the build left out, and why. A record the loader cannot
 * parse or the generator cannot render is skipped with a warning rather
 * than failing the whole site: one malformed record must never stall every
 * later rebuild (the site would stay up but stale, hour after hour, with
 * the fallback failing silently).
 */
export interface SkippedRecord {
  id: string;
  reason: string;
}

export interface DbRecord {
  specVersion: string;
  id: string;
  state: "init" | "draft" | "registered" | "deleted";
  createdAt: string;
  registeredAt?: string;
  deletedAt?: string;
  source?: SourceTriple;
}

export interface StatementEntry {
  id: string;
  signature: string;
  /** Spec 2 only: the statement's universe parameters, in declaration order. */
  levelParams?: string[];
  /** Spec 2 only: the tagged definition's body as the inspector pretty-printed
   * it, in core notation (`Exists fun p => …`). Carried, not shown: the
   * author's source text — with its notation — remains the displayed form of
   * every statement, and this raw rendering would read worse beside it. */
  body?: string;
  startLine?: number;
  endLine?: number;
  doc?: string;
}

/** `Lean.BinderInfo`'s constructor names, as the telescope records them. */
export type BinderKind = "default" | "implicit" | "strictImplicit" | "instImplicit";

/**
 * A spec-2 proof's type as the archive's inspector read it: a chain of
 * hypotheses — each a statement constant with its universe instantiation and
 * binder kind, in binder order, duplicates kept — ending in the concluded
 * statement. The edge as the author wrote it; `conclusion` and `assumptions`
 * are derived from it at load (`src/database.ts`), never stored.
 */
export interface ProofTelescope {
  hypotheses: Array<{ statement: string; levels: string[]; binder: BinderKind }>;
  conclusion: { statement: string; levels: string[] };
}

export interface AnnotationSection {
  title: string;
  markdown: string;
}

export interface ConceptEntry {
  id: string;
  path: string;
  title: string;
  type?: string;
  description: string;
  sections?: AnnotationSection[];
  imports: string[];
  mathlibImports?: string[];
  sourceText: string;
  statements: StatementEntry[];
}

export interface ProofEntry {
  id: string;
  path: string;
  /** Spec 2 only: the proof's universe parameters, in declaration order. */
  levelParams?: string[];
  /** Spec 2 only: the proof's telescope. Absent from a spec-1 record. */
  telescope?: ProofTelescope;
  /** The concluded statement. Stored by a spec-1 record; derived from the
   * telescope for a spec-2 one, so the network and the pages read one shape. */
  conclusion: string;
  /** The assumed statements as a sorted set. Stored (spec 1) or derived
   * (spec 2) like `conclusion`. */
  assumptions: string[];
  description: string;
  sections?: AnnotationSection[];
}

/** A point in PDF user space: 1-based page, points from the bottom-left
 * corner, and the TeX mode the marker was typeset in (`v` between
 * paragraphs, `h` inside a line). The viewer's boundary rule needs the mode:
 * geometry alone cannot tell a vertical-mode destination from an inline one
 * that TeX pushed to the start of the next line. */
export interface PaperMarkPoint {
  page: number;
  x: number;
  y: number;
  mode: "v" | "h";
}

/** One marked passage of the paper, in document order. The card the viewer
 * shows beside it is decided by `kind`: a concept, a proof, or a whole
 * submission (own id or a directly required package's record). */
export interface PaperMark {
  id: string;
  kind: "concept" | "proof" | "submission";
  begin: PaperMarkPoint;
  end: PaperMarkPoint;
}

/** The derived reflowable web rendering of a paper (`paper.web`), present
 * iff the archive's derivation succeeded. `format` pins the deriving tool so
 * the site build can gate old bundles against the vendored viewer's
 * supported schema set; `bundle` names the sealed tar (index, protobuf
 * blocks, fonts, schema) in the capture registry, bare-hex digest like every
 * recorded digest. */
export interface PaperWebEntry {
  format: {
    tool: string;
    rev: string;
    /** sha256 of the bundle's `schema/latex.proto`, bare hex. */
    schema: string;
  };
  bundle: {
    digest: string;
    bytes: number;
    registryBlob?: string;
  };
}

/** The `paper` key of a build output: the compiled document's identity and
 * its marks. The PDF bytes themselves live in the capture registry
 * (`registryBlob`) and are fetched into the papers cache before a build. */
export interface PaperEntry {
  folder: string;
  main: string;
  engine: string;
  pdf: {
    digest: string;
    bytes: number;
    pages: number;
    registryBlob?: string;
  };
  /** `[width, height]` per page, in points. */
  pageSizes: Array<[number, number]>;
  marks: PaperMark[];
  web?: PaperWebEntry;
}

/** The dependency capture the archive sealed for this record: the pins the
 * validated build actually ran under. The archive records a record's pins
 * twice — here and in `manifest.leanVersion`/`.mathlibVersion` — and the
 * environment a record belongs to is the manifest's `leanVersion`. Declared
 * here along with the sealed file manifest used to verify source navigation.
 * Local builds can carry only the environment pins. */
export interface CaptureEntry {
  /** The pins. Stored by a spec-1 record; a spec-2 record stores neither —
   * its environment is the row `manifest.leanVersion` names. */
  leanToolchain?: string;
  mathlibCommit?: string;
  formatVersion?: number;
  digest?: string;
  sourceCommit?: string;
  registryBlob?: string;
  /** The per-file inventory of the sealed tar. Spec 1 only: the reference
   * reader addresses the capture tar by it. A spec-2 record stores none. */
  files?: CaptureFile[];
  /** Spec 2 only: the sealed tar's size and member count. */
  bytes?: number;
  fileCount?: number;
  /** Spec 2 only: the `references` layer beside the capture — the concept
   * sources and their `.ilean` files as one small tar, downloaded whole and
   * verified by digest (`src/references.ts`). */
  references?: CaptureReferences;
}

export interface CaptureFile { path: string; bytes: number; sha256: string }

/** The `references` layer of a spec-2 record's capture manifest: a plain
 * ustar (10240-byte blocking) of `./concepts/package/**.lean` and
 * `./concepts/lib/**.ilean`, media type `application/vnd.lax.references.v1+tar`.
 * `registryBlob` is the digest address the archive pushed it to. */
export interface CaptureReferences {
  digest: string;
  bytes: number;
  registryBlob?: string;
}

/**
 * The `certificate` key of a spec-2 record, present exactly when the record
 * has proofs: the record of the Certify phase. `lake comparator` of the
 * judge's toolchain held the record's proofs (the Solution) to the Challenge
 * — every edge stated over the concept packages alone — under the listed
 * kernels and exited 0. `bundle` is the digest of the five generated files
 * (Challenge, Solution, comparator config, lakefile, manifest), a further
 * layer of the record's capture manifest, fetched and verified like one;
 * `challenge` is `Challenge.lean` verbatim, the one artifact that states in
 * Lean exactly what was certified, so the site shows it without a fetch;
 * `challengeExportSha256` is the digest of the Challenge export the judge
 * compared against, for a rerun to match; `solutionExportSha256` the digest
 * of the Solution export beside it (the judge reads both frozen exports in a
 * container of its own). The latter is absent from a record certified before
 * the judge was split off, so a reader tolerates its absence.
 */
export interface CertificateEntry {
  judge: { toolchain: string; comparatorExitCode: number };
  kernels: string[];
  bundle: { formatVersion: number; digest: string; registryBlob?: string };
  challengeExportSha256: string;
  solutionExportSha256?: string;
  challenge: string;
}

export interface BuildOutput {
  specVersion: string;
  id: string;
  captureId?: string;
  /** Absent only from a record predating captures, or a local `lax build`. */
  capture?: CaptureEntry;
  manifest: Manifest;
  abstract: string;
  requiredByConcepts: string[];
  requiredByProofs: string[];
  concepts: ConceptEntry[];
  proofs: ProofEntry[];
  paper?: PaperEntry;
  /** Spec 2 only, and only on a record with proofs. */
  certificate?: CertificateEntry;
}
