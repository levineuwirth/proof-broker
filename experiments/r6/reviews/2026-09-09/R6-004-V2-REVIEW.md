# R6-004 revision 2 review — two remaining corrections

Reviewed on 2026-09-09. Revision 2 repairs the reported v1 mutations, and its
recorded results reproduce. The pre-live credential requirement remains open:
the reconstruction-context equality check is still missing, and the final
checkpoint gate does not bind the contents of its case population to the frozen
contract. Neither finding demonstrates acceptance of an invalid Lean proof.

Evidence: [review record](R6-004-V2-REVIEW.json),
[fresh focused/audit regression results](R6-004-V2-REGRESSIONS.json), and
[disposable mutation program](r6_004_v2_review_probes.py).

From the repository root, reproduce the remaining context and checkpoint probes
with a new output path:

```bash
python3 -B experiments/r6/reviews/2026-09-09/r6_004_v2_review_probes.py /tmp/r6-004-v2-probes-new.json
```

The program proves that each unmodified copy passes first. It then changes only
disposable copies. The context mutation recomputes the scan entries, report
commitment, event chain and seal, so stale scan provenance is not its detector.
The checkpoint probes call the submitted recount, including its Python
`py_compile` subprocess. No adapter, native episode or Lean replay is rerun.

## What holds

- All 62 recorded checks match the checkpoint hashes/counts and the module's
  exact 25 / 5 / 32 case sets, with no duplicates and no failing record.
- All 25 focused controls and all 32 artifact controls pass when executed again
  on disposable copies. This includes the previous review's regressions and
  twelve historical audits.
- The five native artifacts re-audit to the reported predicates. Independent
  hash recomputation confirms 111 events and 685 sealed entries.
- The 9,986 prior files match. All 719 files from the first review's snapshot
  that belong to the v1 checkpoint or its two policy/lock files remain unchanged.
- V2 retention excluding `final-checks.json` is exactly 700 files, 8,559,691
  apparent bytes, 246 distinct contents and 4,812,273 unique-content bytes.
- The two findings in the reflected response are the same header matched as
  Authorization at offset 52 and token at offset 59. There are no unexpected
  disclosures in the declared bundle or disclosures in publication-accepted
  episodes in the fresh recount.
- The source locks match, and the scan report's hashes/lengths are now checked
  after disclosure and evidence-binding diagnostics.

## Keep the two component route names

The route decision is accepted. `recovery_started` names
`credential_http_fixture_v2`; the unchanged R6-003 consumer emits
`recovery_finished` with `openai_responses_http_fixture_v1`. The auditor checks
that specific pair and the `previous_policy_sha256` relationship, along with
the certificate envelope's binding to the older component. Those names describe
the components that actually emit the records. Copying the consumer solely to
make the names identical would not improve this evidence.

The frozen scanner coverage declaration is also useful. `config()` compares
the version, representations, forms, decompression limit and finalization order
to the implementation constants. The remaining traversal/path policy strings
are declared in the policy and their behavior is in the hash-bound source; they
are not additional comparisons performed by `config()` itself.

## 1. Reconstruction context can still contradict the frozen obligation

Locations: [credential_audit.py](../../credential_audit.py), `check_payload`
at line 179 and `check_proof` at line 433; compare
[provider_audit.py](../../provider_audit.py), lines 82–85.

R6-003 checked both preparation and reconstruction contexts against each other
and the frozen local context. V2 restores the preparation comparison, but not
the reconstruction comparison. The shared proof checker validates the two hash
fields of `context_validated` against their respective files; it does not assert
that the captured context equals the frozen context.

The probe changes `stages/reconstruct/output/context.json` so that its `target`
is the string `False`, updates `captured_context_sha256`, and recomputes the
publication scan, terminal commitments and seal. The full auditor returns:

```json
{"accepted": true, "proof_accepted": true, "publication_accepted": true}
```

The altered context explicitly differs from the frozen context. The proof
export and kernel records are unchanged and still concern the original
arithmetic obligation. This demonstrates an accepted contradiction in the
evidence chain, **not** that Lean proved `False`.

Restore the explicit equality check for a completed reconstruction. Add a
mutation that updates the context receipt and scan provenance as this probe
does; it must reject for the context mismatch itself.

## 2. The recount validates names of directories, not the complete case contract

Locations: [credential_final_checks.py](credential_final_checks.py), `recount`
at line 54; [test_credentials.py](../../test_credentials.py), `finalize_copy`
at line 530.

The recount correctly rejects a missing expected episode directory or process
log. It still trusts the suite's own `expected_cases`, does not require the
checkpoint's `passed` flag, and does not cross-bind each directory's episode
case/outcome/seal to its corresponding native-suite result.

Each of these mutations first confirms the unmodified copy passes:

| Mutation | Result |
| --- | --- |
| Delete `scan_unreadable_directory` from the focused checks and their recorded expected set; update count and checkpoint hash | Recount passes with 61 checks, although the frozen source still requires 62 |
| Replace `d1_missing_credential` with a copy of `d1_valid`, keeping all five directory names and the original suite records | Recount passes with 62 checks; the alleged missing-credential control now reports a successful proof |
| Set `checkpoint.json` to `passed: false` | Recount nevertheless returns `passed: true` |

The second mutation copies an internally valid episode; no proof or seal is
corrupted. The error is that a different control now occupies an expected
control's directory and disagrees with the corresponding suite record. The
recount's population check accepts the names without checking that relationship.

The mid-run helper explains one part of the gap: `finalize_copy` rewrites a
partial suite's expected set to its completed prefix and declares it passed so
the publication-gate probes can proceed. The final recount currently accepts
that weaker contract too.

The final gate should require completed checkpoint status, exact case sets from
the frozen module for **all** suites, and an explicit mapping from each native
case to its task, policy case, expected predicates and retained seal. Cross-check
the native-suite record against the re-audited episode. Keep the partial-run
publication checks separate from the complete-checkpoint gate; tests should
not require weakening the latter to reach the former.

## Remaining diagnostic qualification

Ordinary canary-bearing file paths are now reported safely. Error-path records
still copy names directly. A symlink named with the canary is correctly rejected
by `publication.scan`, but the report re-emits the complete canary in
`irregular_entries[0].name`. The reproduction is:

```python
with tempfile.TemporaryDirectory() as directory:
    root = Path(directory)
    target = root / "ordinary.txt"
    target.write_text("clean")
    (root / canary).symlink_to(target)
    report = publication.scan([root], canary, nonce)
    assert report["accepted"] is False
    assert canary in json.dumps(report)
```

This is not an accepted-publication bypass. It limits the claim that diagnostic
records never re-emit the value. Apply the safe path representation to traversal
errors, irregular entries and root identities as well as ordinary file entries.

## Reporting and population details

The report's sentence “Twenty audit mutations are coherently rehashed and
resealed” should read **14 resealed episode mutations and three checkpoint-gate
mutations**. The 32 audit cases are two retained-only audits, those 17 mutations,
twelve historical audits and one preservation check.

The saved recount reports 734 files. Before this review added any files, a fresh
recount scanned 738: the generated `final-checks.json` is now present, along
with three ignored review bytecode files whose timestamps follow the original
recount. The latter files are in the declared review-directory root, so they
are scanned despite being ignored by Git. This explains the current population
difference; 734 is the original scan observation, not a stable count of files
selected for a commit. New review records also expand that directory's scan
population. The original recount was preserved.

`recorded_not_recomputed: 0` holds for the original five episode trees. The
retained-only controls correctly report the omitted build products separately;
their coverage should continue to be distinguished from the original trees.

## Next step

Keep v1 and v2 as the reviewed records. Restore reconstruction-context equality
and finish the complete-checkpoint contract, with controls for the accepted
mutations above. Extend safe path diagnostics and correct the mutation-population
sentence. Then collect the corrected checkpoint under its new source/policy
lock before closeout.

The live-policy requirement remains open. Submitted source, policies and episode
artifacts were not modified by this review. Only review artifacts were added;
nothing was committed or pushed.
