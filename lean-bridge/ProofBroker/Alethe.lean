/-
Alethe proof ADT + walker (Lean side of the M1 Alethe walker
arc).

The SDK ([sdk/lib/alethe.ml]) parses cvc5's alethe-2024 trace
into a step list and exposes it across the FFI via the
[parse_alethe_proof] method (see [ProofBroker.Bridge]). This
module mirrors the parsed structure on the Lean side and walks
it step-by-step, producing a kernel proof term — the "cert IS
the proof" architectural play, parallel to the Tier-1 Farkas
term-mode closer for Tier-1 certs but for Tier-3 alethe-2024.

Trust model. The OCaml-side [Tier3_alethe.verify] runs a
provenance-level check (every step references valid premises,
the proof walks to the empty clause). The walker here does the
*soundness* work: per-step elaboration into a Lean expression
that the kernel independently typechecks when the goal mvar is
assigned. Audit H1: no axiom is introduced; a walker failure
on an unsupported rule is a tactic failure, with the existing
omega fallback re-running (closer chain in
[ProofBroker.Tactic.closeOrFail]).

Rule coverage. The walker handles a substantial slice of
cvc5's alethe-2024 rule set, organized into clusters:

* **clausal** — `assume` (seeded from top-level
  `Proof.assumes`), `resolution` (n-ary, finds pivots itself),
  `or`, `false`, the empty-`(cl)` closing step.
* **arithmetic** — `la_generic`, `la_mult_neg`. Discharged by
  a scoped `omega` call; the cert drives the surrounding proof
  skeleton, the arithmetic leaves are decided.
* **equality** — `refl`, `symm`, `trans`, `cong`. Kernel proof
  reconstruction (no decision procedure); the `cong` case uses
  `Lean.Meta.mkCongr` over a left-fold of premise equations.
* **trust-tagged leaves** — `hole`, `rare_rewrite`. cvc5's
  "trust me" tags, re-derived via omega independently of the
  annotation. Audit H1: a hole whose clause isn't an
  omega-tautology fails the walker, never admitted on tag.
* **boolean cleanup** — `implies`, `equiv1`, `equiv2`,
  `not_and`, `and_neg`. Constructed via `Classical.em` case
  analysis on the relevant Props.
* **`equiv_simplify`** — propositional-equality tautologies
  matched against a curated pattern set (reflexivity, double
  negation, And/Or idempotence). New patterns added
  incrementally as cvc5 traces demand them.

`Sexp → Expr` covers LIA-shaped terms (`Int`, arithmetic ops,
comparisons, `not`, `True`/`False`, `or`/`and`/`=>`), plus a
generic UF-application fallback for `(f a₁ … aₙ)` over local
free vars (so `cong` works for any in-scope UF symbol).

Production integration. `ProofBroker.Tactic.tryAletheWalkerLIA`
wires the walker into the LIA arm of `closeOrFailPrimary`. The
shared `walkProofIntoGoal` helper distinguishes refutation
traces (final clause empty `(cl)`) from direct traces, and uses
`MVarId.falseOrByContra` to expose `¬goal` as a hypothesis for
non-`False` user goals. Walker failure falls through to omega.

Real cvc5 dispatches still hit rules outside the covered set
(e.g. `equiv_pos1`/`equiv_pos2` 3-literal Boolean tautologies);
those fall through to omega, preserving audit H1. Extending
coverage to the remaining long-tail rules is the next iteration.
-/

import Lean
import ProofBroker.Bridge

namespace ProofBroker.Alethe

open Lean

/-- The parsed shape of an Alethe S-expression: a leaf atom
    (variable, keyword, literal) or a nested list. Mirrors the
    OCaml [Alethe.Sexp.t]; the FFI encoding (see
    [parse_alethe_proof] in [sdk/ffi/proof_broker_ffi.ml]) renders
    atoms as JSON strings and lists as JSON arrays. -/
inductive Sexp where
  | atom : String → Sexp
  | list : List Sexp → Sexp
  deriving Repr, BEq, Inhabited

/-- Decode an FFI-shaped JSON value into an `Sexp`. Strings →
    atoms; arrays → lists; anything else is a decoding error. -/
partial def Sexp.fromJson? : Json → Except String Sexp
  | .str s => .ok (.atom s)
  | .arr xs => do
    let parts ← xs.toList.mapM Sexp.fromJson?
    return .list parts
  | other =>
    .error s!"expected JSON string/array for Alethe Sexp, got: {other.compress}"

/-- An individual Alethe step from the parsed proof. The
    [conclusion] field corresponds to the [(cl …)] form's
    literals (after named-ref expansion); [args] and [premises]
    are rule-specific; [discharge] is the set of subproof
    assumptions discharged at this step (only populated for
    subproof-closing steps). -/
structure Step where
  id : String
  rule : String
  clause : List Sexp
  args : Option (List Sexp)
  premises : Option (List String)
  discharge : Option (List String)
  deriving Repr, Inhabited

private def sexpListFromJson? (j : Json) : Except String (List Sexp) :=
  match j with
  | .arr xs => xs.toList.mapM Sexp.fromJson?
  | _ => .error s!"expected JSON array, got: {j.compress}"

private def stringListFromJson? (j : Json) : Except String (List String) :=
  match j with
  | .arr xs => xs.toList.mapM (fun
      | .str s => .ok s
      | other => .error s!"expected string element, got: {other.compress}")
  | _ => .error s!"expected JSON array of strings, got: {j.compress}"

def Step.fromJson? (j : Json) : Except String Step := do
  let id ← match j.getObjValAs? String "id" with
    | .ok s => pure s
    | .error e => .error e
  let rule ← match j.getObjValAs? String "rule" with
    | .ok s => pure s
    | .error e => .error e
  let clauseJ ← match j.getObjVal? "clause" with
    | .ok v => pure v
    | .error _ => .error "missing 'clause'"
  let clause ← sexpListFromJson? clauseJ
  let args ← match j.getObjVal? "args" with
    | .error _ => pure none
    | .ok v => do
      let xs ← sexpListFromJson? v
      pure (some xs)
  let premises ← match j.getObjVal? "premises" with
    | .error _ => pure none
    | .ok v => do
      let xs ← stringListFromJson? v
      pure (some xs)
  let discharge ← match j.getObjVal? "discharge" with
    | .error _ => pure none
    | .ok v => do
      let xs ← stringListFromJson? v
      pure (some xs)
  return { id, rule, clause, args, premises, discharge }

/-- A top-level Alethe `assume` (the input hypotheses; each
    `assume`-rule step in the proof references one of these by
    id). On the home-system side these correspond to the
    negated-goal literals plus any hypothesis the original goal
    carried into the SMT call. -/
structure Assume where
  id : String
  literal : Sexp
  deriving Repr, Inhabited

def Assume.fromJson? (j : Json) : Except String Assume := do
  let id ← match j.getObjValAs? String "id" with
    | .ok s => pure s
    | .error e => .error e
  let litJ ← match j.getObjVal? "literal" with
    | .ok v => pure v
    | .error _ => .error "missing 'literal'"
  let literal ← Sexp.fromJson? litJ
  return { id, literal }

/-- The full parsed proof: top-level assumes, the step list (in
    declaration order), and the subproof anchor ids (M3 scope —
    not consumed by M1). -/
structure Proof where
  assumes : List Assume
  steps : List Step
  anchors : List String
  deriving Repr, Inhabited

def Proof.fromJson? (j : Json) : Except String Proof := do
  let assumesJ ← match j.getObjVal? "assumes" with
    | .ok v => pure v
    | .error _ => .error "missing 'assumes'"
  let assumes ← match assumesJ with
    | .arr xs => xs.toList.mapM Assume.fromJson?
    | _ => .error "'assumes' is not an array"
  let stepsJ ← match j.getObjVal? "steps" with
    | .ok v => pure v
    | .error _ => .error "missing 'steps'"
  let steps ← match stepsJ with
    | .arr xs => xs.toList.mapM Step.fromJson?
    | _ => .error "'steps' is not an array"
  let anchorsJ ← match j.getObjVal? "anchors" with
    | .ok v => pure v
    | .error _ => .error "missing 'anchors'"
  let anchors ← stringListFromJson? anchorsJ
  return { assumes, steps, anchors }

open ProofBroker (FfiError pbCall decodeEnvelope)

/-- Parse a cvc5 alethe-2024 trace into an `Alethe.Proof` via the
    SDK's [parse_alethe_proof] FFI method. Failure modes: parser
    errors (raised from OCaml as `alethe_parse_error`), envelope
    decode errors (malformed FFI response), and Alethe-shape
    decode errors (FFI returned an unexpected shape). -/
def runParseAletheProof (proofText : String) : Except FfiError Proof := do
  let input := Json.mkObj [("proof", Json.str proofText)]
  let payload ← decodeEnvelope (pbCall "parse_alethe_proof" input.compress)
  match Proof.fromJson? payload with
  | .ok p => pure p
  | .error e =>
    .error (.decodeError s!"decoding alethe proof: {e}" none)

/- ============================================================
   Walker: Alethe proof → Lean kernel proof term
   ============================================================ -/

open Lean Meta Elab Tactic

/-- Walker context: maps Alethe atom names to Lean expressions
    (typically local hypotheses or free variables from the goal's
    context). Populated by `mkContext`, which scans the current
    goal's `LocalContext` and harvests every named local
    declaration. The walker uses this map to resolve atoms during
    `Sexp → Expr` translation. -/
structure WalkerContext where
  vars : NameMap Expr
  deriving Inhabited

/-- Walker state: map from step id to `(proof, clause)` — the
    `Expr` proving that step's clause, paired with the clause's
    literal list (in `Sexp` form). The literal list is needed by
    `resolution`: pivot finding compares literals, and the
    `Or`-injection that builds the resolvent proof needs each
    leftover literal's position. For non-resolution rules the
    clause list is just the step's stated `clause`; for
    `resolution` it is the computed resolvent (equal as a set to
    the stated clause; literal order follows the left-fold). -/
structure WalkerState where
  proven : NameMap (Expr × List Sexp)
  deriving Inhabited

abbrev WalkerM := StateRefT WalkerState MetaM

private def lookupStep (id : String) : WalkerM (Expr × List Sexp) := do
  let st ← get
  match st.proven.find? (Name.mkSimple id) with
  | some pc => pure pc
  | none => throwError m!"alethe walker: step '{id}' not proven yet"

private def storeStep (id : String) (e : Expr) (clause : List Sexp)
    : WalkerM Unit :=
  modify fun st =>
    { st with proven := st.proven.insert (.mkSimple id) (e, clause) }

/-- Build a [WalkerContext] from the current goal's local
    context. Every named hypothesis / free var becomes an atom
    binding. Anonymous locals are skipped (Alethe atoms always
    have names). -/
def mkContext : TacticM WalkerContext := do
  let lctx ← getLCtx
  let mut vars : NameMap Expr := {}
  for decl in lctx do
    unless decl.isImplementationDetail do
      vars := vars.insert decl.userName decl.toExpr
  return { vars }

/- ----------------------------------------------------------------
   Sexp → Expr (LIA scope)

   Atoms are looked up in the context, parsed as Int literals,
   or recognized as `true`/`false` constants. Lists are dispatched
   on the head atom; the recognized heads are the LIA-shaped ones
   the Alethe printer emits (`+`, `-`, `*`, `<=`, `<`, `>=`, `>`,
   `=`, `not`, `or`, `and`, `cl`, `=>`, `true`, `false`).
   ---------------------------------------------------------------- -/

/-- Parse an Alethe integer-shaped atom: either a plain integer
    `"-3"`/`"3"` or a rational denominator-1 form `"3/1"`/`"-3/1"`
    (cvc5's alethe-2024 printer normalizes integers as
    rationals). Returns `none` for anything else. -/
private def parseIntAtom (s : String) : Option Int := do
  let s := s.trim
  if s.isEmpty then none
  else
    let (numStr, denomOk) :=
      match s.splitOn "/" with
      | [n] => (n, true)
      | [n, "1"] => (n, true)
      | _ => ("", false)
    if denomOk then numStr.toInt? else none

/-- Build an `Int`-typed numeral in the exact form omega's
    literal recognizer (`Expr.nat?` / `Expr.int?`) accepts:
    `@OfNat.ofNat Int ⟨rawNatLit k⟩ inst`. Two subtleties:
    * the `OfNat` form is required — a bare `Int.ofNat k`
      constructor is treated as an opaque atom by omega;
    * the inner `Nat` index must be a {e raw} literal
      (`Expr.lit (.natVal k)` via `mkRawNatLit`) — `mkNatLit`
      wraps it in another `OfNat.ofNat`, and `Expr.nat?`'s
      `let lit (.natVal n) := n` match then fails, again
      leaving the literal an opaque atom.
    Negative literals wrap the nonneg numeral in `Neg.neg`. -/
private def mkIntLit (n : Int) : MetaM Expr := do
  let intTy := mkConst ``Int
  let mkNonneg (k : Nat) : MetaM Expr :=
    mkAppOptM ``OfNat.ofNat #[some intTy, some (mkRawNatLit k), none]
  if n < 0 then
    mkAppM ``Neg.neg #[← mkNonneg n.natAbs]
  else
    mkNonneg n.toNat

/- Translate an Alethe `Sexp` to a Lean `Expr`. The recognized
   shapes cover the LIA fragment: integer literals,
   variable/hypothesis references, arithmetic (`+`/`-`/`*`),
   comparisons (`<=`/`<`/`>=`/`>`/`=`), logical connectives
   (`not`/`and`/`or`/`=>`), and the clausal `cl` constructor
   (empty `(cl)` → `False`; one-literal `(cl L)` → `L`;
   many-literal `(cl L1 L2 ...)` → `L1 ∨ L2 ∨ ...`). Other
   shapes raise a clear `throwError` so the omega fallback can
   re-run. `sexpToExpr` / `listToExpr` / `andOrChain` are
   mutually recursive — hence the `mutual` block. -/
mutual

partial def sexpToExpr (ctx : WalkerContext) : Sexp → MetaM Expr
  | .atom s => do
    if s = "true" then return mkConst ``True
    if s = "false" then return mkConst ``False
    match parseIntAtom s with
    | some n => mkIntLit n
    | none =>
      match ctx.vars.find? (Name.mkSimple s) with
      | some e => return e
      | none =>
        throwError m!"alethe walker: unknown atom '{s}' \
                      (not an integer literal, not in scope)"
  | .list xs => listToExpr ctx xs

partial def listToExpr (ctx : WalkerContext) : List Sexp → MetaM Expr
  | [.atom "+", a, b] => do
    mkAppM ``HAdd.hAdd #[← sexpToExpr ctx a, ← sexpToExpr ctx b]
  | [.atom "-", a, b] => do
    mkAppM ``HSub.hSub #[← sexpToExpr ctx a, ← sexpToExpr ctx b]
  | [.atom "-", a] => do
    mkAppM ``Neg.neg #[← sexpToExpr ctx a]
  | [.atom "*", a, b] => do
    mkAppM ``HMul.hMul #[← sexpToExpr ctx a, ← sexpToExpr ctx b]
  | [.atom "<=", a, b] => do
    mkAppM ``LE.le #[← sexpToExpr ctx a, ← sexpToExpr ctx b]
  | [.atom "<", a, b] => do
    mkAppM ``LT.lt #[← sexpToExpr ctx a, ← sexpToExpr ctx b]
  | [.atom ">=", a, b] => do
    mkAppM ``GE.ge #[← sexpToExpr ctx a, ← sexpToExpr ctx b]
  | [.atom ">", a, b] => do
    mkAppM ``GT.gt #[← sexpToExpr ctx a, ← sexpToExpr ctx b]
  | [.atom "=", a, b] => do
    mkAppM ``Eq #[← sexpToExpr ctx a, ← sexpToExpr ctx b]
  | [.atom "not", a] => do
    return mkApp (mkConst ``Not) (← sexpToExpr ctx a)
  | (.atom "and") :: rest => andOrChain ctx ``And rest
  | (.atom "or") :: rest => andOrChain ctx ``Or rest
  | (.atom "cl") :: rest =>
    -- `(cl)` is the empty clause = False. `(cl L)` is just L.
    -- `(cl L1 L2 ...)` is `L1 ∨ L2 ∨ ...` (right-associative).
    match rest with
    | [] => return mkConst ``False
    | [lit] => sexpToExpr ctx lit
    | _ => andOrChain ctx ``Or rest
  | [.atom "=>", a, b] => do
    let aE ← sexpToExpr ctx a
    let bE ← sexpToExpr ctx b
    return mkForall .anonymous .default aE bE
  -- Generic application fallback. Used by `cong` to translate
  -- `(f a1 … an)` into `f a1 … an` for UF symbols. The head is
  -- looked up in `ctx.vars` (UF symbols are local free vars in
  -- the home-system goal); arguments recurse through
  -- `sexpToExpr`. Falls through to the catch-all error if the
  -- head is not in scope, keeping unrecognized shapes as honest
  -- failures rather than silently building ill-typed apps.
  | (.atom name) :: args => do
    match ctx.vars.find? (Name.mkSimple name) with
    | some fE => do
      let argEs ← args.mapM (sexpToExpr ctx)
      Lean.Meta.mkAppM' fE argEs.toArray
    | none =>
      throwError m!"alethe walker: unsupported applied head '{name}' \
                    (not a recognized operator, not in local scope)"
  | other =>
    throwError m!"alethe walker: unsupported Sexp shape: \
                  ({String.intercalate " " (other.map fun s => reprStr s)})"

/-- Right-associate a list of literals into an n-ary `And`/`Or`
    chain. Empty list collapses to `True` (for `And`) / `False`
    (for `Or`) — but the callers only ever pass non-empty lists. -/
partial def andOrChain (ctx : WalkerContext) (conn : Name)
    : List Sexp → MetaM Expr
  | [] => return mkConst (if conn = ``And then ``True else ``False)
  | [lit] => sexpToExpr ctx lit
  | lit :: rest => do
    let lE ← sexpToExpr ctx lit
    let restE ← andOrChain ctx conn rest
    mkAppM conn #[lE, restE]

end

/- ----------------------------------------------------------------
   Clause manipulation: negation, injection, case analysis

   A clause `(cl L1 … Ln)` is the right-associated disjunction
   `L1 ∨ … ∨ Ln` (empty → `False`, singleton → `L1`). These
   helpers build and destruct that structure as Lean proof
   terms; they are the substrate `resolution` is built on.
   ---------------------------------------------------------------- -/

/-- Sexp-level literal negation: `(not X)` ↦ `X`, `X` ↦
    `(not X)`. Involutive, so two literals are complementary iff
    `negateLit a == b`. -/
def negateLit : Sexp → Sexp
  | .list [.atom "not", x] => x
  | other => .list [.atom "not", other]

/-- True iff the literal is syntactically `(not _)`. Picks which
    side of a complementary pair carries the `Not` (i.e. is the
    function in the `Not p` ≡ `p → False` application). -/
def isNotForm : Sexp → Bool
  | .list [.atom "not", _] => true
  | _ => false

/-- The clause-as-Prop of a literal list (`(cl …)` semantics:
    empty → `False`, singleton → the literal, n-ary → the
    right-associated `∨`). -/
def clauseTypeOf (ctx : WalkerContext) (lits : List Sexp) : MetaM Expr :=
  sexpToExpr ctx (Sexp.list (.atom "cl" :: lits))

/-- Given a proof of `target[idx]`, build a proof of the whole
    clause `⋁target` via the right `Or.inl`/`Or.inr` chain. -/
partial def injectLit (ctx : WalkerContext) (target : List Sexp)
    (idx : Nat) (litProof : Expr) : MetaM Expr := do
  match target, idx with
  | [_], 0 => pure litProof
  | (l :: rest), 0 => do
    let aTy ← sexpToExpr ctx l
    let bTy ← clauseTypeOf ctx rest
    mkAppOptM ``Or.inl #[some aTy, some bTy, some litProof]
  | (l :: rest), (k + 1) => do
    let aTy ← sexpToExpr ctx l
    let bTy ← clauseTypeOf ctx rest
    let inner ← injectLit ctx rest k litProof
    mkAppOptM ``Or.inr #[some aTy, some bTy, some inner]
  | _, _ =>
    throwError m!"alethe walker: injectLit index {idx} out of \
                   range for a {target.length}-literal clause"

/-- Case-analyse `clauseProof : ⋁lits`. For each disjunct, call
    `handler idx litProof` (which must return a proof of
    `resultTy`); chain the cases with `Or.elim`. -/
partial def casesClause (ctx : WalkerContext) (clauseProof : Expr)
    (lits : List Sexp) (resultTy : Expr)
    (handler : Nat → Expr → MetaM Expr) : MetaM Expr := do
  match lits with
  | [] => throwError "alethe walker: casesClause on an empty clause"
  | [_] => handler 0 clauseProof
  | (l :: rest) => do
    let lTy ← sexpToExpr ctx l
    let restTy ← clauseTypeOf ctx rest
    let lamL ← withLocalDeclD `hl lTy fun hl => do
      mkLambdaFVars #[hl] (← handler 0 hl)
    let lamR ← withLocalDeclD `hr restTy fun hr => do
      let body ← casesClause ctx hr rest resultTy
        (fun i p => handler (i + 1) p)
      mkLambdaFVars #[hr] body
    mkAppOptM ``Or.elim
      #[some lTy, some restTy, some resultTy,
        some clauseProof, some lamL, some lamR]

/-- Binary clausal resolution. `(eA : ⋁A)` and `(eB : ⋁B)` must
    contain a complementary literal pair (the pivot). Produces
    `(proof, R)` with `R = (A∖pivot) ++ (B∖pivot)` and
    `proof : ⋁R`. The proof case-splits `eA`: the pivot disjunct
    case-splits `eB` and closes the complementary pair with
    `False.elim`; every non-pivot disjunct is injected into `R`
    at its post-erasure position. Throws if no pivot exists. -/
def binaryResolve (ctx : WalkerContext)
    (eA : Expr) (A : List Sexp) (eB : Expr) (B : List Sexp)
    : MetaM (Expr × List Sexp) := do
  let pivot? : Option (Nat × Nat) := Id.run do
    for i in [0:A.length] do
      for j in [0:B.length] do
        if negateLit A[i]! == B[j]! then
          return some (i, j)
    return none
  match pivot? with
  | none =>
    throwError m!"alethe walker: resolution premises share no \
                   complementary literal — no pivot"
  | some (i, j) => do
    let aIsNot := isNotForm A[i]!
    let R := A.eraseIdx i ++ B.eraseIdx j
    let resultTy ← clauseTypeOf ctx R
    let aLen1 := A.length - 1
    let proof ← casesClause ctx eA A resultTy (fun i' hA' => do
      if i' == i then
        casesClause ctx eB B resultTy (fun j' hB' => do
          if j' == j then
            -- complementary pair: the `Not`-side applied to the
            -- other gives `False`, eliminated into `resultTy`.
            let falseProof :=
              if aIsNot then mkApp hA' hB' else mkApp hB' hA'
            mkAppOptM ``False.elim #[some resultTy, some falseProof]
          else
            let pos := aLen1 + (if j' < j then j' else j' - 1)
            injectLit ctx R pos hB')
      else
        injectLit ctx R (if i' < i then i' else i' - 1) hA')
    return (proof, R)

/- ----------------------------------------------------------------
   Rule elaborators
   ---------------------------------------------------------------- -/

/-- An Alethe top-level `(assume id L)`: the proof of `L` is the
    Lean hypothesis in scope whose type is definitionally equal
    to `L`. Mirrors how cvc5 names assumes — they correspond to
    the goal's named hypotheses / the negated-goal literal. If no
    matching hypothesis is found, throws so the omega fallback
    can run.

    Note: Alethe `assume`s are a distinct top-level command form
    (parsed into `Proof.assumes`, not `Proof.steps`); `walkProof`
    seeds them into the walker state before walking the steps. -/
private def elabAssumeLiteral (ctx : WalkerContext) (id : String)
    (literal : Sexp) : WalkerM Expr := do
  let stmt ← sexpToExpr ctx literal
  -- Search the local context for a hypothesis whose type is
  -- definitionally equal to the assume's stated literal.
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    if ← isDefEq decl.type stmt then
      return decl.toExpr
  throwError m!"alethe walker: assume '{id}' states {stmt}, \
                 but no local hypothesis matches that type"

/-- `(cl (not false))` from a `false`-rule step — the standard
    premise for the final empty-cl resolution. The proof of
    `¬False` (≡ `False → False`) is the identity. -/
private def elabFalseStep (_ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause with
  | [.list [.atom "not", .atom "false"]] =>
    let falseExpr := mkConst ``False
    pure (.lam .anonymous falseExpr (.bvar 0) .default, s.clause)
  | _ =>
    throwError m!"alethe walker: 'false' rule expects clause \
                   (cl (not false)), got {repr s.clause}"

/-- `or` rule: restates a single premise — whose one literal is
    an n-ary `(or L1 … Ln)` — as the {e clause} `(cl L1 … Ln)`.
    The Prop is unchanged (`clauseTypeOf [(or L1 … Ln)]` and
    `clauseTypeOf [L1, …, Ln]` are the same right-associated
    `∨`), so the elaborator forwards the premise's proof term but
    swaps in the step's own flattened literal list — that
    re-grouping is exactly what lets `resolution` peel the
    individual literals afterwards. -/
private def elabOr (s : Step) : WalkerM (Expr × List Sexp) := do
  match s.premises with
  | some [p] => do
    let (proof, _) ← lookupStep p
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'or' rule expects exactly one \
                   premise, got {repr s.premises}"

/-- `resolution`: n-ary clausal resolution. Alethe's `resolution`
    is a left-fold of binary resolutions over the premise list;
    each binary step cancels one complementary literal pair
    (`binaryResolve` finds the pivot — cvc5 does not list pivots
    explicitly). The result `(proof, clause)` carries the
    computed resolvent; for a closing step the resolvent is the
    empty clause and the proof has type `False`. -/
private def elabResolution (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.premises with
  | some (p0 :: rest) => do
    let (e0, c0) ← lookupStep p0
    let mut acc : Expr × List Sexp := (e0, c0)
    for pi in rest do
      let (ei, ci) ← lookupStep pi
      acc ← binaryResolve ctx acc.1 acc.2 ei ci
    return acc
  | _ =>
    throwError m!"alethe walker: 'resolution' needs at least one \
                   premise, got {repr s.premises}"

/- ----------------------------------------------------------------
   Equality cluster: `refl` / `symm` / `trans` / `cong`.

   These are the rules cvc5's `alethe-2024` emits for the UF /
   equality fragment. None of them touch a decision procedure
   (unlike `la_generic` / `la_mult_neg` which omega-discharge a
   tautological leaf): they reconstruct the kernel proof from the
   premises directly, so the resulting proof terms are axiom-free
   (no `propext` / `Classical.choice`, just `Eq.rec` underneath).
   ---------------------------------------------------------------- -/

/-- `refl`: a leaf rule with no premises, concluding `(cl (= t t))`
    for any term `t`. The walker requires LHS and RHS to be
    syntactically identical at the Sexp level (the form cvc5
    emits after preprocessing); the proof term is `Eq.refl t`. -/
private def elabRefl (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause with
  | [.list [.atom "=", lhs, rhs]] => do
    unless lhs == rhs do
      throwError m!"alethe walker: 'refl' expects (= t t) with \
                     identical sides, got (= {repr lhs} {repr rhs})"
    let lhsE ← sexpToExpr ctx lhs
    let proof ← mkAppM ``Eq.refl #[lhsE]
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'refl' expects clause \
                   (cl (= t t)), got {repr s.clause}"

/-- `symm`: one premise proving `(= t u)`, conclusion `(= u t)`.
    The proof term is `Eq.symm` of the premise. -/
private def elabSymm (s : Step) : WalkerM (Expr × List Sexp) := do
  match s.premises with
  | some [p] => do
    let (eP, _) ← lookupStep p
    let proof ← mkAppM ``Eq.symm #[eP]
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'symm' expects exactly one \
                   premise, got {repr s.premises}"

/-- `trans`: n premises proving `(= t1 t2)`, `(= t2 t3)`, …,
    `(= t_{n} t_{n+1})`, conclusion `(= t1 t_{n+1})`. The proof
    term is the left-fold of `Eq.trans` over the premise list.
    A single-premise `trans` is a no-op (passthrough). -/
private def elabTrans (s : Step) : WalkerM (Expr × List Sexp) := do
  match s.premises with
  | some (p0 :: rest) => do
    let (e0, _) ← lookupStep p0
    let mut acc := e0
    for pi in rest do
      let (ei, _) ← lookupStep pi
      acc ← mkAppM ``Eq.trans #[acc, ei]
    pure (acc, s.clause)
  | _ =>
    throwError m!"alethe walker: 'trans' expects at least one \
                   premise, got {repr s.premises}"

/-- `cong`: n premises proving `(= a₁ b₁)`, …, `(= aₙ bₙ)`,
    conclusion `(= (f a₁ … aₙ) (f b₁ … bₙ))`. The proof term is
    built by left-folding `Lean.Meta.mkCongr` over the premise
    list, starting from `Eq.refl f`. `mkCongr` collapses the
    `Eq.refl f` seed into `mkCongrArg` automatically, then chains
    through `mkCongr`'s general case for each subsequent
    argument — so the resulting term is a curried congruence
    cascade (`(f a₁) a₂ = (f b₁) b₂` etc.) matching Lean's own
    curried application convention.

    Implementation works at the `Expr` level rather than the
    `Sexp` level so it handles built-in operator atoms uniformly:
    LHS and RHS are translated via `sexpToExpr` (which knows
    `(+ a b)` → `mkAppM ``HAdd.hAdd …`, `(not a)` → `Not a`, UF
    `(f x)` → applied free var, etc.), then `pids.length` apps
    are peeled off the LHS via `Expr.appFn!` to expose the
    operator with its implicit/typeclass args bound. `Eq.refl
    opE` becomes the fold seed.

    Concretely: for `cong h : x = y ⊢ (= (+ x z) (+ y z))` over
    `Int`, `lhsE = @HAdd.hAdd Int Int Int inst x z` has 6 app
    levels (4 implicit + 2 explicit); stripping 2 (= 1 premise,
    since the cong is only over the `x = y` arg) gives
    `@HAdd.hAdd Int Int Int inst x` — but wait, that strips one
    explicit AND not the right one. Actually cvc5 emits cong with
    a premise per arg position, so for binary ops the trace has
    two premises; stripping 2 gives `@HAdd.hAdd Int Int Int
    inst`, the right operator to seed mkCongr from. Mismatched
    arities or differing operators throw. -/
private def elabCong (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause, s.premises with
  | [.list [.atom "=", lhsSexp, rhsSexp]], some pids => do
    let lhsE ← sexpToExpr ctx lhsSexp
    let rhsE ← sexpToExpr ctx rhsSexp
    let lhsArity := lhsE.getAppNumArgs
    let rhsArity := rhsE.getAppNumArgs
    unless lhsArity == rhsArity do
      throwError m!"alethe walker: 'cong' app-arity mismatch: \
                     LHS has {lhsArity} app levels, RHS has \
                     {rhsArity}"
    unless pids.length ≤ lhsArity do
      throwError m!"alethe walker: 'cong' has {pids.length} \
                     premises but LHS only has {lhsArity} app \
                     levels (translated form: {lhsE})"
    let mut opE := lhsE
    let mut opERhs := rhsE
    for _ in [0:pids.length] do
      opE := opE.appFn!
      opERhs := opERhs.appFn!
    unless ← Meta.isDefEq opE opERhs do
      throwError m!"alethe walker: 'cong' operator heads differ \
                     after stripping {pids.length} explicit args: \
                     {opE} vs {opERhs}"
    let mut acc ← mkAppM ``Eq.refl #[opE]
    for pid in pids do
      let (eqProof, _) ← lookupStep pid
      acc ← Lean.Meta.mkCongr acc eqProof
    pure (acc, s.clause)
  | _, _ =>
    throwError m!"alethe walker: 'cong' expects clause \
                   (cl (= LHS RHS)) with a premise list, got \
                   clause {repr s.clause}, premises {repr s.premises}"

/-- Shared omega-discharge helper. Translates the step's clause to
    a `Prop`, spawns a synthetic mvar, runs `falseOrByContra` into
    a `False` goal, and dispatches to the `MetaM`-level `omega`
    entry over the local hypotheses. Mirrors `omegaTactic`'s
    frontend. Returns the instantiated mvar (the proof term) paired
    with the step's clause. -/
private def omegaDischargeClause (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  let clauseProp ← sexpToExpr ctx (Sexp.list (.atom "cl" :: s.clause))
  let mvar ← mkFreshExprSyntheticOpaqueMVar clauseProp
  match ← mvar.mvarId!.falseOrByContra with
  | none => pure ()        -- goal closed by falseOrByContra itself
  | some gFalse =>
    gFalse.withContext do
      let hyps := (← getLocalHyps).toList
      Lean.Elab.Tactic.Omega.omega hyps gFalse
  return (← instantiateMVars mvar, s.clause)

/-- LIA-tautology leaf rules (`la_generic`, `la_mult_neg`). The
    step's clause is a linear-arithmetic tautology — its negation
    is LIA-unsatisfiable, with the Farkas multipliers carried in
    `:args`. cvc5 treats these as proof *leaves*: there is no
    finer cert content below them, so the walker discharges the
    clause with a scoped `omega` call (the architectural decision
    recorded in the M1.γ scoping — omega-ing the leaf mirrors
    Alethe's own structure). `omega` is axiom-free; the cert
    drives the surrounding proof skeleton (resolution /
    congruence / boolean cleanup), the arithmetic leaves are
    decided. -/
private def elabLiaLeaf (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) :=
  omegaDischargeClause ctx s

/-- `hole` / `rare_rewrite`: cvc5's *trust-tagged* leaf forms.
    `hole` is cvc5's "admit the conclusion without proof" step
    (carrying a `TRUST_THEORY_REWRITE` annotation on real traces);
    `rare_rewrite` is a step justified by cvc5's RARE rewrite
    system. Audit H1 forbids trusting either tag: the walker
    re-derives the clause from scratch via the same omega-discharge
    used for LIA leaves, so the resulting proof term goes through
    the kernel independently of cvc5's annotation. Clauses outside
    omega's scope (e.g. pure propositional / theory tautologies
    omega can't handle) surface as `throwError`; the closer
    chain's omega fallback then re-runs at the outer level. The
    point is *never* to admit on tag — the trust gate stays at
    `[propext, Quot.sound]`. -/
private def elabTrustTaggedLeaf (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) :=
  omegaDischargeClause ctx s

/- ----------------------------------------------------------------
   Boolean-cleanup cluster: `implies` / `equiv1` / `equiv2` /
   `not_and` / `and_neg`.

   cvc5 emits these during the SAT-side normalization of Tier-3
   traces — turning implications, propositional equivalences, and
   conjunctions into clausal form for the resolution layer. Proofs
   are constructed directly from the premise via `Classical.em`
   case analysis on the relevant Prop, then injected into the
   resulting clausal disjunction. The footprint grows to
   `[propext, Classical.choice, Quot.sound]` (via `em`) but stays
   within the standard classical baseline — no new trust axioms.
   `equiv_simplify` is deferred to a follow-up: its clauses are
   propositional-equality tautologies (`(= (= a a) true)` etc.)
   that need a different discharge mechanism (propext + `Iff`
   reflexivity, not omega).
   ---------------------------------------------------------------- -/

/-- `implies`: from premise `(=> a b)` proving `a → b`, derive
    `(cl (not a) b)` ≡ `¬a ∨ b`. Proof: case-split `a` with
    `Classical.em`; if `a`, the premise gives `b` (right disjunct);
    if `¬a`, that is the left disjunct. -/
private def elabImplies (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause, s.premises with
  | [.list [.atom "not", a], b], some [p] => do
    let (impH, _) ← lookupStep p
    let aE ← sexpToExpr ctx a
    let bE ← sexpToExpr ctx b
    let notAE := mkApp (mkConst ``Not) aE
    let resultTy ← mkAppM ``Or #[notAE, bE]
    let posCase ← withLocalDeclD `ha aE fun ha => do
      let hb := mkApp impH ha
      let inj ← mkAppOptM ``Or.inr #[some notAE, some bE, some hb]
      mkLambdaFVars #[ha] inj
    let negCase ← withLocalDeclD `hna notAE fun hna => do
      let inj ← mkAppOptM ``Or.inl #[some notAE, some bE, some hna]
      mkLambdaFVars #[hna] inj
    let em ← mkAppM ``Classical.em #[aE]
    let proof ← mkAppOptM ``Or.elim
      #[some aE, some notAE, some resultTy, some em, some posCase, some negCase]
    pure (proof, s.clause)
  | _, _ =>
    throwError m!"alethe walker: 'implies' expects clause \
                   (cl (not a) b) with one premise (=> a b), got \
                   clause {repr s.clause}, premises {repr s.premises}"

/-- `equiv1`: from premise `(= a b)` (propositional equality),
    derive `(cl (not a) b)` ≡ `¬a ∨ b` — the forward direction.
    Proof: case-split `a`; if `a`, transport via `Eq.mp` to get
    `b`; if `¬a`, that is the left disjunct. -/
private def elabEquiv1 (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause, s.premises with
  | [.list [.atom "not", a], b], some [p] => do
    let (eqH, _) ← lookupStep p
    let aE ← sexpToExpr ctx a
    let bE ← sexpToExpr ctx b
    let notAE := mkApp (mkConst ``Not) aE
    let resultTy ← mkAppM ``Or #[notAE, bE]
    let posCase ← withLocalDeclD `ha aE fun ha => do
      let hb ← mkAppM ``Eq.mp #[eqH, ha]
      let inj ← mkAppOptM ``Or.inr #[some notAE, some bE, some hb]
      mkLambdaFVars #[ha] inj
    let negCase ← withLocalDeclD `hna notAE fun hna => do
      let inj ← mkAppOptM ``Or.inl #[some notAE, some bE, some hna]
      mkLambdaFVars #[hna] inj
    let em ← mkAppM ``Classical.em #[aE]
    let proof ← mkAppOptM ``Or.elim
      #[some aE, some notAE, some resultTy, some em, some posCase, some negCase]
    pure (proof, s.clause)
  | _, _ =>
    throwError m!"alethe walker: 'equiv1' expects clause \
                   (cl (not a) b) with one premise (= a b), got \
                   clause {repr s.clause}, premises {repr s.premises}"

/-- `equiv2`: from premise `(= a b)`, derive `(cl a (not b))` ≡
    `a ∨ ¬b` — the backward direction. Proof: case-split `b`; if
    `b`, transport backwards via `Eq.mpr` to get `a`; if `¬b`,
    that is the right disjunct. -/
private def elabEquiv2 (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause, s.premises with
  | [a, .list [.atom "not", b]], some [p] => do
    let (eqH, _) ← lookupStep p
    let aE ← sexpToExpr ctx a
    let bE ← sexpToExpr ctx b
    let notBE := mkApp (mkConst ``Not) bE
    let resultTy ← mkAppM ``Or #[aE, notBE]
    let posCase ← withLocalDeclD `hb bE fun hb => do
      let ha ← mkAppM ``Eq.mpr #[eqH, hb]
      let inj ← mkAppOptM ``Or.inl #[some aE, some notBE, some ha]
      mkLambdaFVars #[hb] inj
    let negCase ← withLocalDeclD `hnb notBE fun hnb => do
      let inj ← mkAppOptM ``Or.inr #[some aE, some notBE, some hnb]
      mkLambdaFVars #[hnb] inj
    let em ← mkAppM ``Classical.em #[bE]
    let proof ← mkAppOptM ``Or.elim
      #[some bE, some notBE, some resultTy, some em, some posCase, some negCase]
    pure (proof, s.clause)
  | _, _ =>
    throwError m!"alethe walker: 'equiv2' expects clause \
                   (cl a (not b)) with one premise (= a b), got \
                   clause {repr s.clause}, premises {repr s.premises}"

/-- `equiv_pos1`: 3-literal Boolean tautology, no premises.
    Conclusion `(cl (not (= a b)) a (not b))` ≡
    `¬(a = b) ∨ a ∨ ¬b`. Proof: nested `Classical.em` case-split.
    If `¬(a = b)`, take the left disjunct. If `a = b`, case on
    `b`: if `b` holds, `Eq.mpr` transports it to `a` for the
    middle disjunct; if `¬b`, take the right disjunct. -/
private def elabEquivPos1 (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause with
  | [.list [.atom "not", .list [.atom "=", a, b]], a',
     .list [.atom "not", b']] => do
    unless a == a' && b == b' do
      throwError m!"alethe walker: 'equiv_pos1' arg mismatch in \
                     clause {repr s.clause}"
    let aE ← sexpToExpr ctx a
    let bE ← sexpToExpr ctx b
    let eqAB ← mkAppM ``Eq #[aE, bE]
    let notEqAB := mkApp (mkConst ``Not) eqAB
    let notBE := mkApp (mkConst ``Not) bE
    let innerOrTy ← mkAppM ``Or #[aE, notBE]
    let resultTy ← mkAppM ``Or #[notEqAB, innerOrTy]
    let posOuter ← withLocalDeclD `eqH eqAB fun eqH => do
      let posInner ← withLocalDeclD `hb bE fun hb => do
        let aProof ← mkAppM ``Eq.mpr #[eqH, hb]
        let innerInl ← mkAppOptM ``Or.inl
          #[some aE, some notBE, some aProof]
        let outerInr ← mkAppOptM ``Or.inr
          #[some notEqAB, some innerOrTy, some innerInl]
        mkLambdaFVars #[hb] outerInr
      let negInner ← withLocalDeclD `hnb notBE fun hnb => do
        let innerInr ← mkAppOptM ``Or.inr
          #[some aE, some notBE, some hnb]
        let outerInr ← mkAppOptM ``Or.inr
          #[some notEqAB, some innerOrTy, some innerInr]
        mkLambdaFVars #[hnb] outerInr
      let emB ← mkAppM ``Classical.em #[bE]
      let body ← mkAppOptM ``Or.elim
        #[some bE, some notBE, some resultTy, some emB,
          some posInner, some negInner]
      mkLambdaFVars #[eqH] body
    let negOuter ← withLocalDeclD `hne notEqAB fun hne => do
      let outerInl ← mkAppOptM ``Or.inl
        #[some notEqAB, some innerOrTy, some hne]
      mkLambdaFVars #[hne] outerInl
    let emEq ← mkAppM ``Classical.em #[eqAB]
    let proof ← mkAppOptM ``Or.elim
      #[some eqAB, some notEqAB, some resultTy, some emEq,
        some posOuter, some negOuter]
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'equiv_pos1' expects clause \
                   (cl (not (= a b)) a (not b)), got {repr s.clause}"

/-- `equiv_pos2`: 3-literal Boolean tautology, no premises.
    Conclusion `(cl (not (= a b)) (not a) b)` ≡
    `¬(a = b) ∨ ¬a ∨ b`. Mirror of `equiv_pos1`: if `a = b` and
    `a` holds, `Eq.mp` transports to `b` for the right disjunct;
    if `¬a`, take the middle disjunct. -/
private def elabEquivPos2 (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause with
  | [.list [.atom "not", .list [.atom "=", a, b]],
     .list [.atom "not", a'], b'] => do
    unless a == a' && b == b' do
      throwError m!"alethe walker: 'equiv_pos2' arg mismatch in \
                     clause {repr s.clause}"
    let aE ← sexpToExpr ctx a
    let bE ← sexpToExpr ctx b
    let eqAB ← mkAppM ``Eq #[aE, bE]
    let notEqAB := mkApp (mkConst ``Not) eqAB
    let notAE := mkApp (mkConst ``Not) aE
    let innerOrTy ← mkAppM ``Or #[notAE, bE]
    let resultTy ← mkAppM ``Or #[notEqAB, innerOrTy]
    let posOuter ← withLocalDeclD `eqH eqAB fun eqH => do
      let posInner ← withLocalDeclD `ha aE fun ha => do
        let bProof ← mkAppM ``Eq.mp #[eqH, ha]
        let innerInr ← mkAppOptM ``Or.inr
          #[some notAE, some bE, some bProof]
        let outerInr ← mkAppOptM ``Or.inr
          #[some notEqAB, some innerOrTy, some innerInr]
        mkLambdaFVars #[ha] outerInr
      let negInner ← withLocalDeclD `hna notAE fun hna => do
        let innerInl ← mkAppOptM ``Or.inl
          #[some notAE, some bE, some hna]
        let outerInr ← mkAppOptM ``Or.inr
          #[some notEqAB, some innerOrTy, some innerInl]
        mkLambdaFVars #[hna] outerInr
      let emA ← mkAppM ``Classical.em #[aE]
      let body ← mkAppOptM ``Or.elim
        #[some aE, some notAE, some resultTy, some emA,
          some posInner, some negInner]
      mkLambdaFVars #[eqH] body
    let negOuter ← withLocalDeclD `hne notEqAB fun hne => do
      let outerInl ← mkAppOptM ``Or.inl
        #[some notEqAB, some innerOrTy, some hne]
      mkLambdaFVars #[hne] outerInl
    let emEq ← mkAppM ``Classical.em #[eqAB]
    let proof ← mkAppOptM ``Or.elim
      #[some eqAB, some notEqAB, some resultTy, some emEq,
        some posOuter, some negOuter]
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'equiv_pos2' expects clause \
                   (cl (not (= a b)) (not a) b), got {repr s.clause}"

/-- De Morgan recursive helper. Given conjuncts `[a₁, …, aₙ]` and
    a proof `h : ¬(a₁ ∧ … ∧ aₙ)` (right-associated), produces a
    proof of `¬a₁ ∨ … ∨ ¬aₙ`. Base case: singleton — `h` is
    already the desired negation. Recursive case: case-split
    `a₁` via `Classical.em`; if it holds, partially apply `h` to
    a suspended conjunction (yielding `¬(a₂ ∧ … ∧ aₙ)`) and
    recurse for the right disjunct; if `¬a₁`, it is the left
    disjunct. -/
private partial def buildNotAnd (ctx : WalkerContext)
    (lits : List Sexp) (h : Expr) : MetaM Expr := do
  match lits with
  | [] => throwError "alethe walker: 'not_and' with empty conjunction"
  | [_] => pure h
  | a :: rest => do
    let aE ← sexpToExpr ctx a
    let notAE := mkApp (mkConst ``Not) aE
    let restAndE ← andOrChain ctx ``And rest
    let restNegs := rest.map (fun lit => Sexp.list [.atom "not", lit])
    let restOrTy ← clauseTypeOf ctx restNegs
    let resultTy ← mkAppM ``Or #[notAE, restOrTy]
    let posCase ← withLocalDeclD `ha aE fun ha => do
      let hPrime ← withLocalDeclD `hrest restAndE fun hrest => do
        let conj ← mkAppM ``And.intro #[ha, hrest]
        let absurd := mkApp h conj
        mkLambdaFVars #[hrest] absurd
      let recProof ← buildNotAnd ctx rest hPrime
      let inj ← mkAppOptM ``Or.inr #[some notAE, some restOrTy, some recProof]
      mkLambdaFVars #[ha] inj
    let negCase ← withLocalDeclD `hna notAE fun hna => do
      let inj ← mkAppOptM ``Or.inl #[some notAE, some restOrTy, some hna]
      mkLambdaFVars #[hna] inj
    let em ← mkAppM ``Classical.em #[aE]
    mkAppOptM ``Or.elim
      #[some aE, some notAE, some resultTy, some em, some posCase, some negCase]

/-- `not_and`: from premise `(not (and a₁ … aₙ))`, derive
    `(cl (not a₁) … (not aₙ))` — De Morgan's law in clausal form.
    The walker strips the `(not _)` wrappers off the clause to
    recover the conjuncts, then `buildNotAnd` recurses on the
    right-associated conjunction structure. -/
private def elabNotAnd (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.premises with
  | some [p] => do
    let (hP, _) ← lookupStep p
    let inner ← s.clause.mapM fun lit =>
      match lit with
      | .list [.atom "not", x] => pure x
      | other =>
        throwError m!"alethe walker: 'not_and' clause literal not \
                       in (not _) form: {repr other}"
    let proof ← buildNotAnd ctx inner hP
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'not_and' expects exactly one \
                   premise, got {repr s.premises}"

/-- Tautology recursive helper. Builds a proof of
    `(a₁ ∧ … ∧ aₙ) ∨ ¬a₁ ∨ … ∨ ¬aₙ` (right-associated in both
    connectives) for a non-empty literal list. Base case `n=1`:
    `Classical.em a₁`. Recursive case: case-split the inner
    recursive result (`rest_and ∨ rest_neg`); if the conjunction
    side fires, case-split `a₁` again to either build the full
    conjunction (left) or inject the head negation (middle); if
    the rest_neg side fires, that is the tail. -/
private partial def buildAndNeg (ctx : WalkerContext)
    (lits : List Sexp) : MetaM Expr := do
  match lits with
  | [] => throwError "alethe walker: 'and_neg' with empty conjunction"
  | [a] => do
    let aE ← sexpToExpr ctx a
    mkAppM ``Classical.em #[aE]
  | a :: rest => do
    let aE ← sexpToExpr ctx a
    let notAE := mkApp (mkConst ``Not) aE
    let restAndE ← andOrChain ctx ``And rest
    let restNegs := rest.map (fun lit => Sexp.list [.atom "not", lit])
    let restOrTy ← clauseTypeOf ctx restNegs
    let recProof ← buildAndNeg ctx rest
    let conjE ← mkAppM ``And #[aE, restAndE]
    let innerOrTy ← mkAppM ``Or #[notAE, restOrTy]
    let resultTy ← mkAppM ``Or #[conjE, innerOrTy]
    let leftBranch ← withLocalDeclD `hRA restAndE fun hRA => do
      let posBranch ← withLocalDeclD `ha aE fun ha => do
        let conj ← mkAppM ``And.intro #[ha, hRA]
        let inj ← mkAppOptM ``Or.inl #[some conjE, some innerOrTy, some conj]
        mkLambdaFVars #[ha] inj
      let negBranch ← withLocalDeclD `hna notAE fun hna => do
        let injInner ← mkAppOptM ``Or.inl #[some notAE, some restOrTy, some hna]
        let injOuter ← mkAppOptM ``Or.inr #[some conjE, some innerOrTy, some injInner]
        mkLambdaFVars #[hna] injOuter
      let em ← mkAppM ``Classical.em #[aE]
      let body ← mkAppOptM ``Or.elim
        #[some aE, some notAE, some resultTy, some em, some posBranch, some negBranch]
      mkLambdaFVars #[hRA] body
    let rightBranch ← withLocalDeclD `hRO restOrTy fun hRO => do
      let injInner ← mkAppOptM ``Or.inr #[some notAE, some restOrTy, some hRO]
      let injOuter ← mkAppOptM ``Or.inr #[some conjE, some innerOrTy, some injInner]
      mkLambdaFVars #[hRO] injOuter
    mkAppOptM ``Or.elim
      #[some restAndE, some restOrTy, some resultTy,
        some recProof, some leftBranch, some rightBranch]

/-- `and_neg`: tautology rule, no premises. Derives the clause
    `(cl (and a₁ … aₙ) (not a₁) … (not aₙ))`. Proof built
    recursively by `buildAndNeg`. The walker verifies the
    negation literals match the conjuncts position-wise — a
    sanity check on the trace's well-formedness. -/
private def elabAndNeg (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause with
  | (.list ((.atom "and") :: conjs)) :: negLits => do
    if conjs.isEmpty then
      throwError m!"alethe walker: 'and_neg' with empty (and) head"
    unless conjs.length == negLits.length do
      throwError m!"alethe walker: 'and_neg' arity mismatch: \
                     {conjs.length} conjuncts vs {negLits.length} \
                     negation literals"
    for pair in negLits.zip conjs do
      let (negLit, conj) := pair
      match negLit with
      | .list [.atom "not", x] =>
        unless x == conj do
          throwError m!"alethe walker: 'and_neg' literal mismatch: \
                         got (not {repr x}), expected (not {repr conj})"
      | _ =>
        throwError m!"alethe walker: 'and_neg' literal not in \
                       (not _) form: {repr negLit}"
    let proof ← buildAndNeg ctx conjs
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'and_neg' expects clause \
                   (cl (and a₁ … aₙ) (not a₁) … (not aₙ)), got \
                   {repr s.clause}"

/-- `not_not`: tautology rule, no premises. Derives the clause
    `(cl (not (not (not φ))) φ)` ≡ `¬¬¬φ ∨ φ`. Proof: case-split
    `φ` with `Classical.em`; if `φ`, that is the right disjunct;
    if `¬φ`, build `¬¬¬φ` as `fun (h : ¬¬φ) => h ¬φ`. Mirror of
    Rocq's `elab_not_not`. -/
private def elabNotNot (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause with
  | [.list [.atom "not", .list [.atom "not", .list [.atom "not", phi]]], phi'] => do
    unless phi == phi' do
      throwError m!"alethe walker: 'not_not' inner/outer formula mismatch: \
                     {repr phi} vs {repr phi'}"
    let phiE ← sexpToExpr ctx phi
    let notPhi := mkApp (mkConst ``Not) phiE
    let notNotPhi := mkApp (mkConst ``Not) notPhi
    let nnnE := mkApp (mkConst ``Not) notNotPhi      -- ¬¬¬φ
    let resultTy ← mkAppM ``Or #[nnnE, phiE]
    let posCase ← withLocalDeclD `hphi phiE fun hphi => do
      let inj ← mkAppOptM ``Or.inr #[some nnnE, some phiE, some hphi]
      mkLambdaFVars #[hphi] inj
    let negCase ← withLocalDeclD `hnphi notPhi fun hnphi => do
      let nnnProof ← withLocalDeclD `hnn notNotPhi fun hnn => do
        mkLambdaFVars #[hnn] (mkApp hnn hnphi)
      let inj ← mkAppOptM ``Or.inl #[some nnnE, some phiE, some nnnProof]
      mkLambdaFVars #[hnphi] inj
    let em ← mkAppM ``Classical.em #[phiE]
    let proof ← mkAppOptM ``Or.elim
      #[some phiE, some notPhi, some resultTy, some em, some posCase, some negCase]
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'not_not' expects clause \
                   (cl (not (not (not phi))) phi), got {repr s.clause}"

/-- `not_or`: from premise `(not (or t_0 … t_n))` and an index arg
    `i`, derive the single-literal clause `(cl (not t_i))`. Proof:
    `fun (hti : t_i) => h (inject t_i into the or at i)`, where
    `h : ¬(or …)` is `(or …) → False`. Mirror of Rocq's
    `elab_not_or`. -/
private def elabNotOr (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause, s.premises, s.args with
  | [_], some [p], some [.atom iStr] => do
    let some i := iStr.toNat?
      | throwError m!"alethe walker: 'not_or' index arg '{iStr}' is not a Nat"
    let (h, premLits) ← lookupStep p
    match premLits with
    | [.list [.atom "not", .list (.atom "or" :: disjuncts)]] => do
      if i ≥ disjuncts.length then
        throwError m!"alethe walker: 'not_or' index {i} out of range for a \
                       {disjuncts.length}-disjunct (or)"
      let tIE ← sexpToExpr ctx disjuncts[i]!
      let proof ← withLocalDeclD `hti tIE fun hti => do
        let orProof ← injectLit ctx disjuncts i hti
        mkLambdaFVars #[hti] (mkApp h orProof)
      pure (proof, s.clause)
    | _ =>
      throwError m!"alethe walker: 'not_or' premise is not (not (or …)): \
                     {repr premLits}"
  | _, _, _ =>
    throwError m!"alethe walker: 'not_or' expects a single-literal clause, \
                   one premise, and one index arg, got clause {repr s.clause}, \
                   premises {repr s.premises}, args {repr s.args}"

/- ----------------------------------------------------------------
   `equiv_simplify`: propositional-equality tautology simplification.

   cvc5's `equiv_simplify` rule emits clauses of the form
   `(cl (= lhs rhs))` where `lhs ↔ rhs` is a propositional
   tautology — reflexivity, double negation, identity-element
   elimination, etc. Unlike the boolean-cleanup rules which take
   a meaningful premise, these are *leaves*: the proof term is
   constructed from the clause's structural shape alone.

   Discharge strategy is a structural pattern matcher rather
   than `omega` (which doesn't handle propext + Iff reasoning)
   or `simp` (which would drag opaque axiom-set growth into the
   trust footprint). Per-pattern hand-built proofs keep the
   audit trail transparent — each supported case has a visible
   `propext (Iff.intro …)` term. Unsupported patterns throw,
   handing control back to the closer chain. New patterns can
   be added incrementally as cvc5 traces demand them.

   Supported patterns (this PR):
   * `(= (= t t) true)`     — reflexivity tautology
   * `(= (not (not a)) a)`  — double negation (Classical)
   * `(= (and a a) a)`      — `And` idempotence
   * `(= (or a a) a)`       — `Or` idempotence
   ---------------------------------------------------------------- -/

/-- Build `(t = t) = True` via `propext (Iff.intro (fun _ ↦ ⟨⟩)
    (fun _ ↦ Eq.refl t))`. No `Classical` needed — both
    directions are constructive. -/
private def buildEqReflTautology (ctx : WalkerContext) (t : Sexp)
    : MetaM Expr := do
  let tE ← sexpToExpr ctx t
  let eqTT ← mkAppM ``Eq #[tE, tE]
  let reflE ← mkAppM ``Eq.refl #[tE]
  let trueE := mkConst ``True
  let trueIntro := mkConst ``True.intro
  let fwdLam ← withLocalDeclD `h eqTT fun h =>
    mkLambdaFVars #[h] trueIntro
  let bwdLam ← withLocalDeclD `h trueE fun h =>
    mkLambdaFVars #[h] reflE
  let iffP ← mkAppM ``Iff.intro #[fwdLam, bwdLam]
  mkAppM ``propext #[iffP]

/-- Build `(¬¬a) = a` via `propext Classical.not_not`. The
    Classical primitive supplies both directions: the backward
    `a → ¬¬a` is constructive, the forward `¬¬a → a` is the
    classical step. -/
private def buildDoubleNegation (ctx : WalkerContext) (a : Sexp)
    : MetaM Expr := do
  let aE ← sexpToExpr ctx a
  let iffP ← mkAppOptM ``Classical.not_not #[some aE]
  mkAppM ``propext #[iffP]

/-- Build `(a ∧ a) = a` via `propext (Iff.intro And.left
    (fun ha ↦ ⟨ha, ha⟩))`. Constructive — no `Classical`. -/
private def buildAndIdem (ctx : WalkerContext) (a : Sexp)
    : MetaM Expr := do
  let aE ← sexpToExpr ctx a
  let aAndA ← mkAppM ``And #[aE, aE]
  let fwdLam ← withLocalDeclD `h aAndA fun h => do
    let p ← mkAppM ``And.left #[h]
    mkLambdaFVars #[h] p
  let bwdLam ← withLocalDeclD `ha aE fun ha => do
    let p ← mkAppM ``And.intro #[ha, ha]
    mkLambdaFVars #[ha] p
  let iffP ← mkAppM ``Iff.intro #[fwdLam, bwdLam]
  mkAppM ``propext #[iffP]

/-- Build `(a ∨ a) = a` via `propext (Iff.intro (fun h ↦
    h.elim id id) Or.inl)`. Constructive — no `Classical`. -/
private def buildOrIdem (ctx : WalkerContext) (a : Sexp)
    : MetaM Expr := do
  let aE ← sexpToExpr ctx a
  let aOrA ← mkAppM ``Or #[aE, aE]
  let fwdLam ← withLocalDeclD `h aOrA fun h => do
    let leftLam ← withLocalDeclD `hL aE fun hL =>
      mkLambdaFVars #[hL] hL
    let rightLam ← withLocalDeclD `hR aE fun hR =>
      mkLambdaFVars #[hR] hR
    let body ← mkAppOptM ``Or.elim
      #[some aE, some aE, some aE, some h, some leftLam, some rightLam]
    mkLambdaFVars #[h] body
  let bwdLam ← withLocalDeclD `ha aE fun ha => do
    let p ← mkAppOptM ``Or.inl #[some aE, some aE, some ha]
    mkLambdaFVars #[ha] p
  let iffP ← mkAppM ``Iff.intro #[fwdLam, bwdLam]
  mkAppM ``propext #[iffP]

/-- `equiv_simplify`: structural pattern matcher on the
    `(= lhs rhs)` clause shape. Each recognized pattern delegates
    to a per-pattern builder; unrecognized shapes throw with the
    supported-pattern list. -/
private def elabEquivSimplify (ctx : WalkerContext) (s : Step)
    : WalkerM (Expr × List Sexp) := do
  match s.clause with
  | [.list [.atom "=", lhs, rhs]] => do
    let proof ← match lhs, rhs with
      | .list [.atom "=", t1, t2], .atom "true" =>
        if t1 == t2 then
          buildEqReflTautology ctx t1
        else
          unsupportedEquivSimplify lhs rhs
      | .list [.atom "not", .list [.atom "not", a]], a' =>
        if a == a' then
          buildDoubleNegation ctx a
        else
          unsupportedEquivSimplify lhs rhs
      | .list [.atom "and", a1, a2], a' =>
        if a1 == a2 && a1 == a' then
          buildAndIdem ctx a1
        else
          unsupportedEquivSimplify lhs rhs
      | .list [.atom "or", a1, a2], a' =>
        if a1 == a2 && a1 == a' then
          buildOrIdem ctx a1
        else
          unsupportedEquivSimplify lhs rhs
      | _, _ =>
        unsupportedEquivSimplify lhs rhs
    pure (proof, s.clause)
  | _ =>
    throwError m!"alethe walker: 'equiv_simplify' expects clause \
                   (cl (= lhs rhs)), got {repr s.clause}"
where
  unsupportedEquivSimplify (lhs rhs : Sexp) : MetaM Expr := do
    throwError m!"alethe walker: 'equiv_simplify' pattern not \
                   recognized: (= {repr lhs} {repr rhs}). Supported \
                   patterns: (= (= t t) true) / (= (not (not a)) a) \
                   / (= (and a a) a) / (= (or a a) a). New patterns \
                   can be added incrementally — see Alethe.lean."

/-- Elaborate a single step: dispatch on `rule` to a per-rule
    elaborator, store the result under the step's `id`. Unknown
    rules throw — the omega fallback in `closeOrFail` catches
    these so the walker is honest about partial coverage.

    `assume` is not handled here: Alethe `assume`s are a separate
    top-level command (`Proof.assumes`), seeded into the walker
    state by `walkProof` before the step list is walked. -/
def elabStep (ctx : WalkerContext) (s : Step) : WalkerM Unit := do
  let (proof, clause) ← match s.rule with
    -- PARITY:walker-rules BEGIN — kept in lockstep with rocq-bridge/src/alethe_walker.ml
    -- (tools/check_walker_parity.py fails CI if the two rule sets diverge)
    | "or" => elabOr s
    | "resolution" => elabResolution ctx s
    | "false" => elabFalseStep ctx s
    | "la_generic" => elabLiaLeaf ctx s
    | "la_mult_neg" => elabLiaLeaf ctx s
    | "refl" => elabRefl ctx s
    | "symm" => elabSymm s
    | "trans" => elabTrans s
    | "cong" => elabCong ctx s
    | "hole" => elabTrustTaggedLeaf ctx s
    | "rare_rewrite" => elabTrustTaggedLeaf ctx s
    | "implies" => elabImplies ctx s
    | "equiv1" => elabEquiv1 ctx s
    | "equiv2" => elabEquiv2 ctx s
    | "equiv_pos1" => elabEquivPos1 ctx s
    | "equiv_pos2" => elabEquivPos2 ctx s
    | "not_and" => elabNotAnd ctx s
    | "and_neg" => elabAndNeg ctx s
    | "not_not" => elabNotNot ctx s
    | "not_or" => elabNotOr ctx s
    | "equiv_simplify" => elabEquivSimplify ctx s
    -- PARITY:walker-rules END
    | other =>
      throwError m!"alethe walker: rule '{other}' not yet \
                     supported (current scope: resolution / or / \
                     false / la_generic / la_mult_neg / refl / \
                     symm / trans / cong / hole / rare_rewrite / \
                     implies / equiv1 / equiv2 / equiv_pos1 / \
                     equiv_pos2 / not_and / and_neg / \
                     equiv_simplify, plus seeded assumes — the \
                     omega fallback in closeOrFail handles any \
                     residual unsupported rules)."
  storeStep s.id proof clause

/-- Walk an Alethe proof and return the `Expr` proving the final
    step's clause. For a closing alethe-2024 proof the last step
    is `(step _ (cl) :rule resolution :premises (...))` and the
    returned expression has type `False`.

    Two phases: (1) seed each top-level `assume` by matching its
    literal against a local hypothesis; (2) fold `elabStep` over
    the step list. The `proven` map keys are both assume ids and
    step ids — Alethe references either uniformly by id. -/
def walkProof (ctx : WalkerContext) (proof : Proof) : MetaM Expr := do
  let initial : WalkerState := { proven := {} }
  let walk : WalkerM Expr := do
    for a in proof.assumes do
      let e ← elabAssumeLiteral ctx a.id a.literal
      storeStep a.id e [a.literal]
    proof.steps.forM (elabStep ctx)
    match proof.steps.getLast? with
    | none =>
      throwError m!"alethe walker: proof has no steps — nothing to \
                     conclude (a well-formed alethe-2024 proof ends \
                     in an empty-clause resolution step)"
    | some last =>
      let (e, _) ← lookupStep last.id
      pure e
  let (result, _) ← walk.run initial
  return result

end ProofBroker.Alethe
