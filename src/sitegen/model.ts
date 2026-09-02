import { PROOF_SUFFIX } from "../config.js";
import type { BuildOutput, ConceptEntry, DbRecord, ProofEntry, StatementEntry } from "../types.js";
import { computeNetwork, type ProofNetwork } from "./network.js";

export interface SiteSubmission {
  record: DbRecord;
  output?: BuildOutput;
}

export interface LocatedConcept { submission: SiteSubmission; output: BuildOutput; concept: ConceptEntry }
export interface LocatedStatement extends LocatedConcept { statement: StatementEntry }
export interface LocatedProof { submission: SiteSubmission; output: BuildOutput; proof: ProofEntry }

function idNumber(id: string): number {
  const match = /^(?:Lax)?(\d+)/i.exec(id);
  return match ? Number(match[1]) : Number.MAX_SAFE_INTEGER;
}

/** Archive ids are numeric identifiers: Lax2 sorts before Lax10. */
export function compareIds(a: string, b: string): number {
  return idNumber(a) - idNumber(b) || a.localeCompare(b);
}

export class SiteModel {
  readonly submissions: SiteSubmission[];
  readonly outputs: BuildOutput[];
  readonly network: ProofNetwork;
  readonly submissionById = new Map<string, SiteSubmission>();
  readonly conceptHome = new Map<string, LocatedConcept>();
  readonly statementHome = new Map<string, LocatedStatement>();
  readonly proofHome = new Map<string, LocatedProof>();
  readonly importers = new Map<string, LocatedConcept[]>();
  readonly statementProofs = new Map<string, LocatedProof[]>();
  /** Submission-level dependencies: the submissions each one builds on. */
  readonly submissionUses = new Map<string, Set<string>>();
  /** The same relation reversed: the submissions that build on each one. */
  readonly submissionUsedBy = new Map<string, Set<string>>();
  /** Each submission's declared supersedes target, bound or not. */
  readonly supersedesClaim = new Map<string, string>();
  /** Bound forward version pointers: the registered successor by superseded id. */
  readonly supersededBy = new Map<string, string>();
  /** The bound pointers reversed: the superseded submission by successor id. */
  private readonly predecessorOf = new Map<string, string>();

  constructor(submissions: SiteSubmission[]) {
    // A deleted record is a tombstone that exists only to retire its id: no
    // page, no listing, no graph node. Filtering here covers every site
    // generator caller, and keys on the state rather than on a missing
    // build-output so a stale output left in a clone changes nothing.
    this.submissions = submissions
      .filter((submission) => submission.record.state !== "deleted")
      .sort((a, b) => compareIds(a.record.id, b.record.id));
    this.outputs = this.submissions.flatMap((submission) => submission.output ? [submission.output] : []);
    this.network = computeNetwork(this.outputs);
    for (const submission of this.submissions) {
      this.submissionById.set(submission.record.id, submission);
      const output = submission.output;
      if (!output) continue;
      for (const concept of output.concepts) {
        // The annotation gate requires a type since 2026-07-27; a record
        // without one is pre-gate data the archive must surface, not render
        // around with an "untyped" fallback.
        if (!concept.type?.trim())
          throw new Error(`concept ${concept.id} declares no type; every concept annotation carries one`);
        const located = { submission, output, concept };
        this.conceptHome.set(concept.id, located);
        for (const statement of concept.statements)
          this.statementHome.set(statement.id, { ...located, statement });
        for (const imported of concept.imports) {
          const values = this.importers.get(imported) ?? [];
          values.push(located);
          this.importers.set(imported, values);
        }
      }
      for (const proof of output.proofs) {
        const located = { submission, output, proof };
        this.proofHome.set(proof.id, located);
        const values = this.statementProofs.get(proof.conclusion) ?? [];
        values.push(located);
        this.statementProofs.set(proof.conclusion, values);
      }
    }
    for (const values of [...this.importers.values(), ...this.statementProofs.values()])
      values.sort((a, b) => a.output.id.localeCompare(b.output.id));
    this.linkSubmissions();
    this.linkVersions();
  }

  /**
   * Version chains, derived from the successors' manifests: a `supersedes`
   * claim is *bound* — and only then nudges readers away from the older
   * version — once its claimant is registered. The control plane admits at
   * most one registered successor per submission; should stale data ever
   * carry two, the lowest id wins so the generated output stays
   * deterministic rather than build-order-dependent.
   */
  private linkVersions(): void {
    for (const submission of this.submissions) {
      const id = submission.record.id;
      const target = submission.output?.manifest.supersedes;
      if (!target || target === id || !this.submissionById.has(target)) continue;
      this.supersedesClaim.set(id, target);
      if (submission.record.state !== "registered") continue;
      const existing = this.supersededBy.get(target);
      if (existing === undefined || compareIds(id, existing) < 0) this.supersededBy.set(target, id);
    }
    for (const [older, newer] of this.supersededBy) this.predecessorOf.set(newer, older);
  }

  /** Whether a registered successor replaces this submission. */
  isSuperseded(id: string): boolean {
    return this.supersededBy.has(id);
  }

  /** Follow bound successors to the newest version; `id` itself when current. */
  latestVersion(id: string): string {
    const seen = new Set([id]);
    let current = id;
    for (;;) {
      const next = this.supersededBy.get(current);
      if (next === undefined || seen.has(next)) return current;
      seen.add(next);
      current = next;
    }
  }

  /** The bound version chain through `id`, oldest first; `[id]` alone when
   * this submission neither supersedes nor is superseded. */
  versionChain(id: string): string[] {
    const chain = [id];
    for (;;) {
      const previous = this.predecessorOf.get(chain[0]!);
      if (previous === undefined || chain.includes(previous)) break;
      chain.unshift(previous);
    }
    for (;;) {
      const next = this.supersededBy.get(chain[chain.length - 1]!);
      if (next === undefined || chain.includes(next)) break;
      chain.push(next);
    }
    return chain;
  }

  /** The chain to present in version-history UI. A draft successor can show
   * the registered history it proposes to extend on its own page without
   * prematurely making that draft the successor on older pages. */
  versionHistory(id: string): string[] {
    const chain = this.versionChain(id);
    const submission = this.submissionById.get(id);
    const target = submission?.record.state === "draft" ? this.supersedesClaim.get(id) : undefined;
    if (!target) return chain;
    const previous = this.versionChain(target);
    return previous.includes(id) ? previous : [...previous, id];
  }

  /** The registered version readers should normally use. A draft that
   * proposes to supersede existing work does not become current until it is
   * registered. */
  currentVersion(id: string): string {
    const submission = this.submissionById.get(id);
    const target = submission?.record.state === "draft" ? this.supersedesClaim.get(id) : undefined;
    return this.latestVersion(target ?? id);
  }

  /**
   * The submission-level dependency relation, unioned from two sources so it
   * neither invents nor loses an edge: every cross-submission reference the
   * content itself makes (a concept importing a foreign concept, a proof
   * naming a foreign statement), plus the packages the two lakefiles require.
   * A reference cannot exist without its require, but a require can be
   * declared without a reference — so the requires are the complete list and
   * the references are the visible reason for most of it.
   *
   * Records that only reserved an id have no dependencies to read and are no
   * one's dependency, so the relation covers exactly the outputs.
   */
  private linkSubmissions(): void {
    const known = new Set(this.outputs.map((output) => output.id));
    for (const id of known) {
      this.submissionUses.set(id, new Set());
      this.submissionUsedBy.set(id, new Set());
    }
    for (const output of this.outputs) {
      const uses = this.submissionUses.get(output.id)!;
      const add = (id: string | undefined) => {
        if (id && id !== output.id && known.has(id)) uses.add(id);
      };
      for (const concept of output.concepts)
        for (const imported of concept.imports) add(this.conceptHome.get(imported)?.output.id);
      for (const proof of output.proofs)
        for (const statement of [proof.conclusion, ...proof.assumptions])
          add(this.statementHome.get(statement)?.output.id);
      // A proof package requires `<id>Proofs`; both halves live in submission `id`.
      for (const pkg of [...output.requiredByConcepts, ...output.requiredByProofs])
        add(pkg.endsWith(PROOF_SUFFIX) ? pkg.slice(0, -PROOF_SUFFIX.length) : pkg);
    }
    for (const [id, uses] of this.submissionUses)
      for (const used of uses) this.submissionUsedBy.get(used)!.add(id);
  }

  /** Transitive closure of a submission relation from `id`, `id` excluded. */
  private submissionClosure(relation: Map<string, Set<string>>, id: string): string[] {
    const found = new Set<string>();
    const visit = (current: string) => {
      for (const next of relation.get(current) ?? []) {
        if (next === id || found.has(next)) continue;
        found.add(next);
        visit(next);
      }
    };
    visit(id);
    return [...found].sort(compareIds);
  }

  /** Every submission this one transitively builds on. */
  submissionUpstream(id: string): string[] {
    return this.submissionClosure(this.submissionUses, id);
  }

  /** Every submission that transitively builds on this one. */
  submissionDownstream(id: string): string[] {
    return this.submissionClosure(this.submissionUsedBy, id);
  }

  upstreamClosure(conceptId: string): LocatedConcept[] {
    const found = new Map<string, LocatedConcept>();
    const visit = (id: string) => {
      const current = this.conceptHome.get(id);
      if (!current || found.has(id) || id === conceptId) return;
      found.set(id, current);
      current.concept.imports.forEach(visit);
    };
    this.conceptHome.get(conceptId)?.concept.imports.forEach(visit);
    return [...found.values()].sort((a, b) => a.concept.id.localeCompare(b.concept.id));
  }

  /** Every concept that transitively imports `conceptId`. */
  downstreamClosure(conceptId: string): LocatedConcept[] {
    const found = new Map<string, LocatedConcept>();
    const visit = (id: string) => {
      for (const importer of this.importers.get(id) ?? []) {
        if (found.has(importer.concept.id) || importer.concept.id === conceptId) continue;
        found.set(importer.concept.id, importer);
        visit(importer.concept.id);
      }
    };
    visit(conceptId);
    return [...found.values()].sort((a, b) => a.concept.id.localeCompare(b.concept.id));
  }
}
