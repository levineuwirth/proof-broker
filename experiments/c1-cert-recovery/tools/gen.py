"""Generate the campaign's Lean files from tools/corpus.py."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import corpus

def main(run_dir):
    lean_dir = os.path.join(run_dir, "lean")
    os.makedirs(lean_dir, exist_ok=True)
    os.makedirs("ir", exist_ok=True)
    n = 0
    for c in corpus.CASES:
        for key, tac in corpus.CLOSERS.items():
            p = os.path.join(lean_dir, f"{c['id']}.{key}.lean")
            open(p, "w").write(corpus.render(c, key, tac))
            n += 1
        open(os.path.join("ir", f"{c['id']}.dump.lean"), "w").write(
            corpus.render_dump(c))
    # held-out: written to heldout/ so they are inspectable, NOT into the run dir
    os.makedirs("heldout", exist_ok=True)
    for c in corpus.HELD_OUT:
        c = dict(c, group="held_out",
                 source="held out for evaluating a later repair — NOT RUN at "
                        "checkpoint 1")
        for key, tac in corpus.CLOSERS.items():
            open(os.path.join("heldout", f"{c['id']}.{key}.lean"), "w").write(
                corpus.render(c, key, tac))
    print(f"generated {n} corpus files in {lean_dir}, "
          f"{len(corpus.CASES)} IR capture files in ir/, "
          f"{len(corpus.HELD_OUT) * len(corpus.CLOSERS)} held-out files in heldout/")

if __name__ == "__main__":
    main(sys.argv[1])
