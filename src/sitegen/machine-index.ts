import { compareEnvironments, type SiteModel } from "./model.js";

/**
 * The site's machine-readable surface: `index.json` and `environments.json`
 * at the site root. Until these existed an agent that wanted to know what the
 * archive holds had to clone `lax-database` or scrape the rendered HTML; the
 * first is a git dependency for a question about titles, and the second
 * breaks whenever the pages change.
 *
 * Both are derived entirely from what the site already renders, so they carry
 * no fact the pages do not. Key order is written out literally and every list
 * has one sorting rule, because the whole site build must be reproducible.
 */

export interface IndexedConcept {
  id: string;
  title: string;
  type: string;
}

export interface IndexedRecord {
  id: string;
  state: string;
  /** The record's environment: its `manifest.leanVersion`. */
  environment: string;
  title: string;
  /** The predecessor this record's manifest claims, bound or not. */
  supersedes?: string;
  /** The registered successor that replaced it, when one exists. */
  supersededBy?: string;
  concepts: IndexedConcept[];
  /** Proof ids; a proof's claim is on its page, not in the index. */
  proofs: string[];
}

export interface RecordIndex {
  records: IndexedRecord[];
}

export interface EnvironmentCount {
  id: string;
  /** Registered records in this environment, superseded ones included: the
   * island's size, which is what `lax init --env` reports to an author. */
  registered: number;
  drafts: number;
}

export interface EnvironmentIndex {
  epoch: string;
  environments: EnvironmentCount[];
}

/** Every record the site renders a page for, in the site's own id order.
 * Records that only reserved an id have no content and are left out, exactly
 * as they are left out of every listing. */
export function recordIndex(model: SiteModel): RecordIndex {
  const records = model.submissions.flatMap((submission): IndexedRecord[] => {
    const output = submission.output;
    if (!output) return [];
    const id = submission.record.id;
    const supersedes = output.manifest.supersedes;
    const supersededBy = model.supersededBy.get(id);
    return [{
      id,
      state: submission.record.state,
      environment: output.manifest.leanVersion,
      title: output.manifest.title,
      ...(supersedes === undefined ? {} : { supersedes }),
      ...(supersededBy === undefined ? {} : { supersededBy }),
      concepts: output.concepts.map((concept) => ({
        id: concept.id,
        title: concept.title,
        type: concept.type!,
      })),
      proofs: output.proofs.map((proof) => proof.id),
    }];
  });
  return { records };
}

/** The epoch and the environments the archive holds work in, epoch first and
 * the rest newest first. The epoch is always listed, even at zero, because it
 * is the answer to "where should I submit" rather than a count. */
export function environmentIndex(model: SiteModel): EnvironmentIndex {
  const counted = new Map<string, EnvironmentCount>([
    [model.epoch, { id: model.epoch, registered: 0, drafts: 0 }],
  ]);
  for (const submission of model.submissions) {
    const environment = model.environmentOf.get(submission.record.id);
    if (environment === undefined) continue;
    const entry = counted.get(environment)
      ?? { id: environment, registered: 0, drafts: 0 };
    if (submission.record.state === "registered") entry.registered += 1;
    else if (submission.record.state === "draft") entry.drafts += 1;
    counted.set(environment, entry);
  }
  const others = [...counted.keys()].filter((id) => id !== model.epoch).sort(compareEnvironments);
  return {
    epoch: model.epoch,
    environments: [model.epoch, ...others].map((id) => counted.get(id)!),
  };
}
