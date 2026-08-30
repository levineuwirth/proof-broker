# Walker replay corpus

A corpus of LIA+UF goals that cvc5 closes, used to measure how much of the
fragment the Alethe walker actually replays (kernel-checked), and to rank the
rules that block the rest. This README plus the committed `coverage.json`
are the durable coverage plan/baseline (the earlier
`.claude/walker-replay-coverage-plan.md` lived in a gitignored directory
and no longer exists).

## Layout

```
goals/<id>.json     hand-authored: { id, description, coq_goal, ir }
traces/<id>.alethe  GENERATED: verbatim cvc5 alethe-2024 trace for that goal
index.json          GENERATED: { "<id>": {result, rules, steps, assumes} }
coverage.json       GENERATED + COMMITTED: the static-coverage baseline (gated)
```

`goals/*.json` are the only hand-edited files. `ir` is a full IR document
(same schema as `examples/`), decoded by `Codec.of_json`. `coq_goal` is the
Coq `Prop` the goal denotes — it must match `ir.goal` (the dynamic replay
proves `coq_goal` by walking the trace, so a mismatch fails under coqc).

A goal may also carry `"replay_skip": "<reason>"`: statically walkable but
excluded from the dynamic replay (an unhandled shape of a supported rule).
It still counts as walkable in the static report; the skip is recorded in
`CorpusReplay.v`.

## Regenerating (needs cvc5 on PATH)

```
opam exec -- dune exec sdk/bin/corpus_gen.exe -- corpus   # traces/ + index.json
python tools/check_walker_coverage.py --write             # coverage.json + report
python tools/gen_corpus_replay.py --write                 # CorpusReplay.v
```

Commit the regenerated artifacts; the diffs are the review surface.

## What CI checks

- `check_walker_coverage.py --check` — report matches committed `coverage.json`
  (schemas job; no build, no solver).
- `gen_corpus_replay.py --check` — `CorpusReplay.v` is in sync with the corpus.
- `dune build` compiles `rocq-bridge/theories/CorpusReplay.v` — the dynamic,
  kernel-checked ground truth that every statically-walkable goal actually
  closes (rocq-bridge job).
- live-drift (blocking since PR #74; the "Walker corpus live-drift" step of
  the rocq-bridge job) — regenerate against CI's cvc5 and fail on any diff.

## Adding a goal

1. Write `goals/<id>.json` (a goal cvc5 can prove `unsat` on the negation).
2. Regenerate (commands above); inspect the coverage report.
3. Commit goal + trace + updated `index.json` / `coverage.json` / `CorpusReplay.v`.
