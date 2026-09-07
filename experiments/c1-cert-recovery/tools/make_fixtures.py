"""Hand-built IR fixtures for the negative-check gate's regressions.

These are not reified from Lean: each one is the smallest IR that exhibits a
specific defect the gate must keep catching, and writing them directly is how
they stay minimal and stable. They live in `ir/` so the gate's ordinary loop
picks them up, and they are listed in tools/negcheck_expectations.py.

  F1_lra_strict_ground — an LRA IR whose whole contradiction is a STRICT
    ground relation (`0 < 0`, compiled `Lt(0)`) sitting next to a genuinely
    vacuous `0 = 0`. Regression for R6 checkpoint-2 review finding 6: reading
    only the compiled form's constant classified `Lt(0)` as vacuous, target
    selection fell through to the irrelevant `Eq(0)` coefficient, and five
    mutations "passed" without ever touching the contradiction.

  F2_eq_negative_multiplier — a witness that needs a NEGATIVE multiplier on an
    equality. Exercises the +/- column split that makes freely-signed equality
    coefficients reachable at all; a split that silently dropped the negative
    half would still pass every other case in the corpus.
"""
import json, os

def numlit(v, ty="Real"):
    return {"node": "NumLit", "value": str(v), "type": ty}

def app(sym, *args):
    return {"node": "App", "symbol": sym, "type_args": [], "args": list(args)}

def var(n):
    return {"node": "Var", "name": n}

def ir(fragment, hyps, goal, free_vars=(), ty="Real"):
    return {
        "ir_version": "1.0",
        "source_system": {"name": "c1-cert-recovery-fixture", "version": "1.0"},
        "tier": "goal",
        "logic_classification": {
            "order": "first_order",
            "first_order_fragment": fragment,
            "features_used": [],
            "decidable_theory": None,
        },
        "goal": {"shell": goal},
        "context": {
            "type_vars": [],
            "free_vars": [{"name": n, "type": ty} for n in free_vars],
            "hypotheses": [{"name": n, "shell": s} for n, s in hyps],
        },
        "type_metadata": {},
        "definitional_metadata": {},
        "library_provenance": {},
    }

FIXTURES = {
    # `hP` compiles to Eq(0) — genuinely vacuous. `strict` is `0 < 0`, which
    # compiles to Lt(0) under LRA: false on its own, and the entire proof.
    "F1_lra_strict_ground": ir(
        "LRA",
        [("hP", {"node": "Eq", "type": "Real",
                 "left": numlit(0), "right": numlit(0)}),
         ("strict", app("LT.lt", numlit(0), numlit(0)))],
        {"node": "Const", "name": "False"}),

    # 2*x = 1 has no integer solution but IS rationally satisfiable, so the
    # witness must come from the equality with a NEGATIVE multiplier against
    # the two bounds: 1*(x <= 0) + 1*(0 <= x) forces x = 0, and -1*(2x - 1)
    # contributes the constant 1 > 0.
    "F2_eq_negative_multiplier": ir(
        "LRA",
        [("hle", app("LE.le", var("x"), numlit(0))),
         ("hge", app("LE.le", numlit(0), var("x"))),
         ("heq", {"node": "Eq", "type": "Real",
                  "left": app("HMul.hMul", numlit(2), var("x")),
                  "right": numlit(1)})],
        {"node": "Const", "name": "False"},
        free_vars=["x"]),
}

if __name__ == "__main__":
    os.makedirs("ir", exist_ok=True)
    for name, doc in FIXTURES.items():
        p = os.path.join("ir", name + ".json")
        with open(p, "w") as fh:
            json.dump(doc, fh, indent=1)
            fh.write("\n")
        print("wrote", p)
