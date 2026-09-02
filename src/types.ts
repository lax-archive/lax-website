/** Data contract consumed from the public lax-db repository. */

export interface Author {
  name: string;
  orcid?: string;
  github?: string;
}

export interface Manifest {
  specVersion: string;
  id: string;
  leanVersion: string;
  mathlibVersion: string;
  title: string;
  authors: Author[];
  bibEntries: string[];
  /** The submission this one replaces; binding once this one is registered. */
  supersedes?: string;
}

export interface SourceTriple {
  repository: string;
  commit: string;
  folder: string;
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
  startLine?: number;
  endLine?: number;
  doc?: string;
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
  conclusion: string;
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

export interface BuildOutput {
  specVersion: string;
  id: string;
  captureId?: string;
  manifest: Manifest;
  abstract: string;
  requiredByConcepts: string[];
  requiredByProofs: string[];
  concepts: ConceptEntry[];
  proofs: ProofEntry[];
  paper?: PaperEntry;
}
