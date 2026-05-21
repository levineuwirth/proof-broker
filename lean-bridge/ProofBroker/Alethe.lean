/-
Alethe proof ADT + walker (Lean side of the M1 Alethe walker
work, in the Lean-side Alethe walker arc).

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
that the kernel will independently typecheck when the goal
mvar is assigned. Audit H1: no axiom is introduced; a walker
failure on an unsupported rule is a tactic failure, with the
existing omega fallback re-running (closer chain in
[ProofBroker.Tactic.closeOrFail]).

M1.β (this PR) scope: **clausal rules only** — `assume`,
`resolution`, `or`, and the empty-`(cl)` closing step. Sexp→Expr
covers LIA-shaped terms (`Int`, arithmetic ops, comparisons,
`not`, `True`/`False`, `or`/`and` connectives) so the
expression layer is ready for the arithmetic rules. Subsequent
PRs add: `la_generic` + `la_mult_neg` (arithmetic), then
`refl` / `symm` / `trans` / `cong` (equality), then the
boolean-cleanup cluster cvc5 emits everywhere (`hole`,
`rare_rewrite`, `equiv_simplify`, `equiv1`/`equiv2`, `implies`,
`and_neg`). Real cvc5 output uses ~14 rules even for a tiny
Farkas proof, so meaningful coverage requires the full set;
this PR's clausal-only walker still falls through to omega on
real cvc5 traces but the architecture is in place to extend.
Unsupported rules surface as `throwError`; the omega fallback
in `closeOrFail` catches them.
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

/-- Walker state: map from step id to the `Expr` proving that
    step's clause (a disjunction of literals — `False` for the
    empty clause). Built up by folding [Step.elab] over the
    proof's step list. -/
structure WalkerState where
  proven : NameMap Expr
  deriving Inhabited

abbrev WalkerM := StateRefT WalkerState MetaM

private def lookupStep (id : String) : WalkerM Expr := do
  let st ← get
  match st.proven.find? (Name.mkSimple id) with
  | some e => pure e
  | none => throwError m!"alethe walker: step '{id}' not proven yet"

private def storeStep (id : String) (e : Expr) : WalkerM Unit :=
  modify fun st => { st with proven := st.proven.insert (.mkSimple id) e }

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
   Rule elaborators (clausal layer)
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

/-- `(cl)` from a `false`-rule step. Alethe's `(step _ (cl (not false)) :rule false)`
    is the standard premise for the final empty-cl resolution. The
    proof of `(cl (not false))` is `(fun (h : False) => h) : ¬False`. -/
private def elabFalseStep (_ctx : WalkerContext) (s : Step) : WalkerM Expr := do
  match s.clause with
  | [.list [.atom "not", .atom "false"]] =>
    -- ¬False ≡ False → False ≡ id : False → False
    let falseExpr := mkConst ``False
    return .lam .anonymous falseExpr (.bvar 0) .default
  | _ =>
    throwError m!"alethe walker: 'false' rule expects clause \
                   (cl (not false)), got {repr s.clause}"

/-- `or` rule: from a single premise that is the n-ary `or` of
    literals, produce the same clause. Alethe's `or` rule
    decomposes a non-clausal Prop of the form `(or L1 L2 ... Ln)`
    into the clause `(cl L1 L2 ... Ln)`. Logically the
    proposition is unchanged (clause IS disjunction at the Prop
    level under our `cl` encoding), so the elaborator just
    returns the premise expression with the same type. -/
private def elabOr (s : Step) : WalkerM Expr := do
  match s.premises with
  | some [p] => lookupStep p
  | _ =>
    throwError m!"alethe walker: 'or' rule expects exactly one \
                   premise, got {repr s.premises}"

/-- `resolution`: clausal resolution between premise clauses.
    Alethe's `resolution` is multi-way (resolves over multiple
    pivot literals in one step). M1.β implements the binary
    case (two premises) for clauses with one or two literals
    each — the most common shape in the boolean-cleanup steps
    that close cvc5 LIA proofs. Larger resolutions surface as
    `throwError`, and the omega fallback runs. -/
private def elabResolution (s : Step) : WalkerM Expr := do
  match s.premises with
  | some [p1, p2] => do
    let e1 ← lookupStep p1
    let e2 ← lookupStep p2
    -- For M1.β we only handle the simplest case: one premise
    -- has type `L`, the other has type `¬L`, and we derive
    -- `False`. This corresponds to the final closing step of
    -- many cvc5 proofs (`(step closing (cl) :rule resolution
    -- :premises (some_L some_neg_L))`).
    let t1 ← inferType e1
    let t2 ← inferType e2
    -- Try e1 : L, e2 : L → False
    let negT1 := mkApp (mkConst ``Not) t1
    if ← isDefEq t2 negT1 then
      return mkApp e2 e1
    -- Or e2 : L, e1 : L → False
    let negT2 := mkApp (mkConst ``Not) t2
    if ← isDefEq t1 negT2 then
      return mkApp e1 e2
    throwError m!"alethe walker: resolution between {t1} and {t2} \
                   is not the simple ¬-elimination shape M1.β \
                   handles (multi-literal clauses + pivot \
                   selection are M1.γ scope)."
  | _ =>
    throwError m!"alethe walker: 'resolution' M1.β scope handles \
                   exactly 2 premises, got {repr s.premises}"

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
    decided.

    Implementation mirrors `omegaTactic`'s frontend: a synthetic
    mvar of the clause type, `falseOrByContra` into a `False`
    goal, then the `MetaM`-level `omega` entry over the local
    hypotheses. -/
private def elabLiaLeaf (ctx : WalkerContext) (s : Step) : WalkerM Expr := do
  let clauseProp ← sexpToExpr ctx (Sexp.list (.atom "cl" :: s.clause))
  let mvar ← mkFreshExprSyntheticOpaqueMVar clauseProp
  match ← mvar.mvarId!.falseOrByContra with
  | none => pure ()        -- goal closed by falseOrByContra itself
  | some gFalse =>
    gFalse.withContext do
      let hyps := (← getLocalHyps).toList
      Lean.Elab.Tactic.Omega.omega hyps gFalse
  instantiateMVars mvar

/-- Elaborate a single step: dispatch on `rule` to a per-rule
    elaborator, store the result under the step's `id`. Unknown
    rules throw — the omega fallback in `closeOrFail` catches
    these so the walker is honest about partial coverage.

    `assume` is not handled here: Alethe `assume`s are a separate
    top-level command (`Proof.assumes`), seeded into the walker
    state by `walkProof` before the step list is walked. -/
def elabStep (ctx : WalkerContext) (s : Step) : WalkerM Unit := do
  let result ← match s.rule with
    | "or" => elabOr s
    | "resolution" => elabResolution s
    | "false" => elabFalseStep ctx s
    | "la_generic" => elabLiaLeaf ctx s
    | "la_mult_neg" => elabLiaLeaf ctx s
    | other =>
      throwError m!"alethe walker: rule '{other}' not yet \
                     supported (current scope: resolution / or / \
                     false / la_generic / la_mult_neg, plus \
                     seeded assumes. Subsequent PRs add \
                     multi-literal resolution and the equality \
                     (cong / refl / trans) + boolean-cleanup \
                     (hole / rare_rewrite / equiv_* / implies / \
                     and_neg) clusters — the omega fallback \
                     handles full cvc5 traces in the meantime)."
  storeStep s.id result

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
      storeStep a.id e
    proof.steps.forM (elabStep ctx)
    match proof.steps.getLast? with
    | none =>
      throwError m!"alethe walker: proof has no steps — nothing to \
                     conclude (a well-formed alethe-2024 proof ends \
                     in an empty-clause resolution step)"
    | some last => lookupStep last.id
  let (result, _) ← walk.run initial
  return result

end ProofBroker.Alethe
