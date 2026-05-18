# Building the Rocq bridge locally

CI builds `rocq-bridge` via `ocaml/setup-ocaml`, which provisions
opam with **its own compiler**. Reproducing that locally matters
because of one sharp edge (audit #17):

## The `ocaml-system` switch trap

If your opam switch was created against the **system** OCaml
(`opam switch create . --packages=ocaml-system`, or
`opam init --compiler=ocaml-system`), installing the Rocq stack
fails — reproducibly, independent of dune version and install
ordering — with:

```
make dunestrap COQ_SPLIT=1 ...
  Invalid_argument("failed to locate Coq kernel package in split
  build mode: rocq-runtime.kernel")
```

`rocq-core` (>= 9.1.1)'s `COQ_SPLIT` build cannot resolve
`rocq-runtime.kernel` when an externally-provided (system) OCaml /
findlib is in play. CI never hits this because `setup-ocaml` uses an
opam-built compiler.

## Supported local setup

Use a **dedicated opam-managed compiler switch** (not
`ocaml-system`), mirroring CI:

```sh
# Pick the compiler CI uses.
opam switch create proof-broker 5.4.0
eval "$(opam env --switch=proof-broker)"

# SDK + Rocq plugin deps (both opam files at repo root).
opam install -y --deps-only --with-test \
  ./proof_broker.opam ./proof_broker_rocq.opam

# Build everything (sdk + rocq-bridge) and run the trust gate.
opam exec -- dune build > rocq_build.log 2>&1 || (cat rocq_build.log; exit 1)
python tools/check_axioms.py --build-output rocq_build.log --bridge rocq
```

`dune build rocq-bridge` alone also works once the deps are in.

### Notes

* `coq-stdlib` (the `Stdlib` theory the `.v` files need) is pulled
  transitively by `proof_broker_rocq.opam`'s `coq-stdlib` dep; on the
  dedicated switch it builds cleanly alongside `rocq-runtime` /
  `coq-core`.
* If `alcotest` fails to install because the system OCaml ships a
  preinstalled `ocamlbuild`, pass `CHECK_IF_PREINSTALLED=false` to the
  `opam install` (only relevant when the host OCaml is also visible).
* The Rocq side was statically audited during the 2026-05 review
  (clean — no `admit`/`Admitted`/added axioms; term-mode is
  `Refine.refine ~typecheck:true` + `ring` + `Qed`). The C3 trust-gate
  parser fix was confirmed against real Coq 9.x `Print Assumptions`
  output by CI's `rocq-bridge` job; this doc closes the remaining
  local-reproducibility gap.
