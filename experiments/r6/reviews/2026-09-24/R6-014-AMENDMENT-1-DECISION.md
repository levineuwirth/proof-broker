# R6-014 amendment 1: decision (post-collection)

The operator decided on 2026-09-24, after the frozen live audit of block 1 was rejected at `revision:history_bound`
([R6-014-BLOCK1-LIVE-AUDIT-REJECTED.json](R6-014-BLOCK1-LIVE-AUDIT-REJECTED.json), commit `6a361a3e`). The decision, verbatim:

> Yes—prepare option 1 for review.
>
> Treat it as a post-collection amendment to the directory-layout check, not as an unchanged preregistered evaluation. Preserve the
> original lock, rejection and collection byte-for-byte, and document when and why the amendment became necessary.
>
> For the repair:
>
> - Derive campaign-owned filenames explicitly, including the source lock whose name differs from the policy prefix. Require the complete
>   expected set and reject unexpected campaign-specific files; ignore unrelated policies.
> - Preserve every existing content, revision-chain, authorization and evidence comparison.
> - Add a shared-directory positive control, plus separate controls for missing required files, unexpected campaign revisions and altered
>   bindings. Confirm the isolated fixtures retain the same accepted case population.
> - Exercise the production directory layout with synthetic evidence first. Do not use the collected outcomes to decide what else the
>   auditor should accept.
>
> Keep analysis deferred. After review, freeze live-evaluation-v2, then audit the unchanged collection. If another production-only mismatch
> appears, retain that rejection and review it separately rather than accumulating exceptions until the collection passes.
>
> No additional transmission or spending is authorized. The eleven consumed slots remain consumed regardless of the eventual audit outcome.
