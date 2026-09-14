# R6-007 — single-call pilot preflight

Status: live boundary built and **frozen disabled**, 2026-09-10. No provider
request has been made and none can be made from the current frozen policy.
This document is the decision point, not a checkpoint report.

## What the single call is for

One request, on D1/70, with the frozen `farkas-lia-v1` prompt and its compiled
`le`/`eq` rows. The model either returns a JSON witness that the SDK verifies as
a Farkas certificate and Lean consumes to a replayed kernel proof, or it does
not. Four outcomes are already distinguishable by existing recorded boundaries:
a verifying witness, a well-formed witness that fails arithmetic verification, a
malformed or refused response, and a transport or provider failure.

This resolves whether an IR-only proposal interface produces anything usable at
all. It is one attempt on one already-solved development obligation, so it
establishes no capability, reliability or benchmark result, and its outcome is
not a measurement. Cohort selection remains the separate next piece of work.

## What changes at the live boundary

Everything downstream of the wire is the reviewed R6-006 v2 machinery — the same
pricing gate and retained sources, the same credential channel, the same Farkas
consumption, the same independent kernel replay. Exactly four things differ, and
each is recorded rather than implied.

| Change | Control |
| --- | --- |
| `live_enabled` becomes true | Requires a complete author authorization record; the flag alone is refused, and the record alone is refused |
| The transport reaches the real endpoint | The proposal stage shares the host network namespace; every other stage keeps `--unshare-all` |
| The client trusts the public CA bundle | Pinned by digest (`8c97794a…`, 121 certificates) and re-checked inside the actor |
| Attribution becomes `live_model_response` | A new proposer identity; no canned receipt is reused and no earlier component is relabelled |

The rehearsal and the live attempt run the **same** actor: same admission, same
credential read, same TLS context, same `connection()` and `handoff()`.
`--mode live` differs only by having no loopback seam and by trusting the pinned
public bundle. The actor re-derives the authorization from the mounted policy
rather than trusting the driver, so a rehearsal-shaped invocation cannot reach
the provider and a live invocation cannot silently fall back to a fixture.

Two limits are stated plainly because they are real. The network namespace is
**shared, not filtered**: this is not an egress allowlist, and destination
control comes from the actor's endpoint check and the audited command. And
`--unshare-all` is given up only for that one stage; user, IPC, PID, UTS and
cgroup namespaces, the capability drop, the cleared environment, the new session
and the supervisor's resource accounting are all retained.

## The ledger is capped at one attempt, not at $5

`total_micro_usd` is **102,400** — exactly one attempt's conditional reservation
under the R6-006 v2 rate basis — with `campaign_attempts: 1`,
`attempts_per_episode: 1`, `automatic_retries: 0` and `redirects: 0`. A
single-call pilot should not be able to spend twice even if something retries,
so the ledger cannot fund a second attempt. Maximum exposure is **$0.102400**,
not the $5 policy ceiling.

## Verified on this host

- TLS to `api.openai.com:443` completes and verifies: TLSv1.3, CN matches, using
  the pinned 121-certificate bundle. Reachability is not a blocker.
- Both pricing sources remain bound and re-extract to the frozen rates.
- 17 boundary controls pass
  ([`test_pilot.py`](test_pilot.py)): policy frozen disabled, authorization
  required/scope/subject, flag-and-record together, CA pinned, live refuses
  fixture inputs, rehearsal requires them, one-attempt ledger, versioned
  attribution, dated snapshot, the network stage keeps every other namespace and
  shares only the network one, the shared stage builder is unchanged, no
  environment credential is read, and the endpoint allowlist is exact.

## What you supply

1. **A credential file.** Any path outside the repository, containing exactly
   one newline-terminated line, mode 0600. The harness mounts it read-only at
   `/credential`, never copies it into the run, never reads an environment
   variable, and removes nothing you did not give it. I have not looked for a
   key and will not.
2. **A signature.** Re-freezing the policy with your name and a UTC timestamp
   writes the authorization record and flips `live_enabled`. Until then the
   frozen policy refuses every live destination.

```bash
# only when you are ready to authorize the one call
rm experiments/r6/policies/responses-live-pilot-v1.json \
   experiments/r6/policies/pilot-harness-v1.sha256.json
python3 -B experiments/r6/pilot_contract.py "<your name>" "<UTC timestamp>"
```

## What is still to build

The live boundary is complete; the episode driver that carries a live response
through preparation, assembly, consumption and replay is not. That is a
mechanical adaptation of `priced_episode_v2` — swap the actor, use the network
stage for the proposal, and version the proposer identity — plus its audit and a
canned rehearsal through the exact live entrypoint. I stopped here because the
next decision is yours, not because the remaining work is uncertain.

Order of operations when you authorize: rehearse through the live entrypoint
with a canned responder, confirm the recorded command shows the intended
destination and namespace, then change only `--mode`.
