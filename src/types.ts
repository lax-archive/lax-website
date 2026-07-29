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
  owners: { githubId: number; handle: string }[];
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
}
