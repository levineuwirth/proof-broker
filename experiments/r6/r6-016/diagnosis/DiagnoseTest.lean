import Diagnose
open Lean Meta Elab R6016Diagnosis

/-! The build's check of `Diagnose`'s attempts (R6-016 harness review, finding 4, the reviewer's resource probe): at every
recursion limit, from 1 upward, each attempt on `↑(2 ^ 16) ≠ 1` returns one of the four outcomes, and none escapes as an
exception; a `resource_exhausted` outcome names the limits. At the default limit, the counterexample is established. -/

def outcomeOf (j : Json) : String := ((j.getObjValD "outcome").getStr?).toOption.getD "<none>"

def detailOf (j : Json) : String := ((j.getObjValD "detail").getStr?).toOption.getD ""

run_meta do
  let a := mkApp (mkConst ``Int.ofNat) (mkApp2 (mkConst ``Nat.pow) (toExpr (2 : Nat)) (toExpr (16 : Nat)))
  let b := toExpr (1 : Int)
  let mut exhausted := 0
  for depth in [1, 2, 3, 4, 5, 6, 7, 8, 16, 32, 64] do
    let results ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with maxRecDepth := depth }) do
        let k ← kernelRfl "probe" a b
        let d ← defeqAt .default false a b k
        let ar ← arithmetic "probe" a b
        let cx ← counterexample "probe" a b
        return #[toJson k, d, ar.getObjValD "omega", ar.getObjValD "grobner", cx])
      (fun ex => throwError m!"an attempt escaped at maxRecDepth {depth}: {ex.toMessageData}")
    for j in results do
      unless ["established", "refused", "resource_exhausted", "unsuccessful"].contains (outcomeOf j) do
        throwError m!"no outcome at maxRecDepth {depth}: {j}"
      if outcomeOf j == "resource_exhausted" then
        exhausted := exhausted + 1
        let named := ((detailOf j).splitOn s!"maxRecDepth {depth}").length > 1
        unless named do throwError m!"the limit is not named: {j}"
  unless exhausted > 0 do throwError "no attempt exhausted a limit; the probe tests nothing"
  let cx ← counterexample "probe" a b
  unless outcomeOf cx == "established" do throwError m!"the counterexample at the default limit: {cx}"
