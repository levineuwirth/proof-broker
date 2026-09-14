# R6-009 v3 audit revision 2 — closeout at d3a22f7

Approved at the canned checkpoint's stated scope. Both P2 findings from the [review of 7240ae5](R6-009-V3-REVIEW.md) are closed. I inspected the repairs, reran the three historical audits and the full copied-artifact control suite, and independently checked the retained bytes and counts. No further blocking finding arose in this review.

The command check now reconstructs the entire sender argv. The retained runtime pin's digest must equal the policy's runtime digest; the runtime and binary inventories and role records must agree with it. The expected stdlib materialization path, interpreter, library mounts, modules, record mounts, sandbox prefix, writable mounts and actor arguments are then derived and compared exactly. Each former passing corruption — foreign stdlib plus role, foreign interpreter plus role, and extra read-only repository mount — rejects at `command:reconstructed_from_pinned_runtime_and_layout`.

The stage check now requires exactly the outcome's three, four or eleven stages. Each must record successful return and cleanup, with the proper frozen limits and event-capture setting. It reads build/replay defaults from the frozen `episode.stage`, whose source is bound to the retained copies; it does not apply the sender's smaller limits to those stages. Both exit-7 corruptions reject at `stages:every_stage_on_the_path_returned`, despite their matching finish receipts.

| Fresh verification | Result |
| --- | --- |
| Current v3 audit | 208 cases, accepted |
| Superseded v2 audit | 208 cases, accepted with explicit superseded status |
| Superseded v1 audit | 169 cases, accepted with explicit superseded status |
| Audit controls | 44: one accepted baseline, 43 rejected mutations; exact names and rejection cases |
| Fresh versus committed audit/control records | Identical parsed values, exact named populations and source digests |
| Current six-run chains and seals | 238 event hashes; 1,596 retained and 36 available ephemeral entries; all match |
| Campaign ledger | 12 rows, four consumed slots, 409,600 µUSD, no open reservations |
| Source lock | `3351d52969a96b84d54944720761b5f1d3d4c70e9955a8118ae6604ba8e616ee`, still verifies |
| Review-start preservation | 42,791 files, zero changed or missing; `.cache` and `__pycache__` excluded |

One wording qualification for the command description: the four credential/TLS paths are the only *unconstrained* source paths. The pinned interpreter and library paths also live outside the repository. Their exact inventory, unlike the ephemeral source names, is fixed. This is a description of the existing check, not a further implementation requirement. Reconstructing recorded paths and validating retained observations also remains distinct from attesting what a host actually executed.

Evidence: [current audit](R6-009-V3-AUDIT2-CLOSEOUT-AUDIT.json), [superseded v2](R6-009-V3-AUDIT2-CLOSEOUT-SUPERSEDED-V2.json), [superseded v1](R6-009-V3-AUDIT2-CLOSEOUT-SUPERSEDED-V1.json), [control suite](R6-009-V3-AUDIT2-CLOSEOUT-CONTROLS.json), and [independent closeout checks](R6-009-V3-AUDIT2-CLOSEOUT-CHECKS.json), produced by [cohort_v3_audit2_closeout.py](cohort_v3_audit2_closeout.py). The checks record the fresh and committed record digests and the scratch preservation inventory's location and digest.

The commit diff from `7240ae5` confirms that the cohort harness sources, v3 policy/lock, six native run directories and campaign ledger are unchanged. I did not rerun the focused native controls or any native episode, compile Lean, or perform kernel replay. No real credential was read and no provider call, signing, commit or push was performed. Only new non-locked closeout files were added; the older review and its findings remain as history.

Proceed to the extended capture-anchor checkpoint. Establish extraction and integrity checks for the census before selecting membership, retain every admission or exclusion with its reason, and freeze manifests and membership before running either experimental arm. The policy remains disabled; this closeout does not authorize cohort spending.
