"""Freeze provenance for the C1-derived synthetic recovery control."""
import difflib
from pathlib import Path
import shutil
import subprocess

import run as r6
from task_spec import C8, D1

BASE='e627efe1ee69638678cc94e3f759d93abd69a160'
ORIGIN='experiments/c1-cert-recovery/runs/20260907-113052/lean/C8_coef_2p18.omega.lean'
ORIGIN_HASH='2c7c2131a28eb87201bbbf3c8793eea751741adc9309ac983af018b239072d0e'
MODEL_COMMIT='573e1686323fe5fc1aa9a41c1d3c20b1175732cd'
MODEL_PATH='lean/RmsNormBracket/RmsNormBracket/Model.lean'


def read_model_reference(model_repo: Path):
    # Reference data only: this source is never imported as an R6 module.
    model=subprocess.check_output(['git','-C',str(model_repo.resolve()),'show',f'{MODEL_COMMIT}:{MODEL_PATH}'])
    if 'def P : ℕ := 18446744069414584321\n'.encode() not in model:
        raise ValueError('Original field definition differs')
    return model


def prepare(*, model_repo: Path):
    if (C8.path/'expected.json').exists() or (C8.path/'manifest.json').exists():
        raise ValueError('C8 is already frozen')
    r6.trusted_sources(C8)
    model=read_model_reference(model_repo)
    source=C8.path/'source'
    source.mkdir(exist_ok=True)
    references={
        'C8.omega.lean':ORIGIN,
        'corpus.py':'experiments/c1-cert-recovery/tools/corpus.py',
        'truth_check.py':'experiments/c1-cert-recovery/tools/truth_check.py',
        'C8.final_ir.json':'experiments/c1-cert-recovery/raw/20260907-113052/C8_coef_2p18.final_ir.json',
    }
    for name,path in references.items():
        data=subprocess.check_output(['git','-C',str(r6.ROOT.parents[1]),'show',f'{BASE}:{path}'])
        (source/name).write_bytes(data)
    if r6.sha(source/'C8.omega.lean')!=ORIGIN_HASH:
        raise ValueError('C1 source revision changed')
    (source/'Model.lean').write_bytes(model)
    capture=D1.capture.read_text().replace(D1.local,C8.local).replace(D1.id,C8.id)
    C8.capture.write_text(capture)
    (C8.path/'context').mkdir(exist_ok=True)
    for name in ['upstream-lake-manifest.json','lean-toolchain']:
        shutil.copyfile(D1.path/name,C8.path/name)
    (C8.path/'upstream-lakefile.toml').write_text(
        'name = "R6C8Control"\n[[require]]\nname = "mathlib"\nscope = "leanprover-community"\nrev = "v4.32.0"\n')
    original=(source/'C8.omega.lean').read_text()
    derived=(C8.path/'Pristine.lean').read_text()
    (C8.path/'derivation.patch').write_text(''.join(difflib.unified_diff(
        original.splitlines(True),derived.splitlines(True),fromfile='source/C8.omega.lean',tofile='Pristine.lean')))
    r6.write_json(C8.path/'source-provenance.json',{
        'repository':'https://github.com/levineuwirth/proof-broker.git','commit':BASE,
        'commit_date':'2026-09-07T10:11:08Z','files':references,
        'files_sha256':{name:r6.sha(source/name) for name in references},
        'definition_reference':{'repository':'https://github.com/JamesPetrie/VerInf.git',
            'commit':MODEL_COMMIT,'source_file':MODEL_PATH,'sha256':r6.sha(source/'Model.lean')},
        'origin_is_anonymous_example':True,
        'environment':'R6 uses the D1/70 Mathlib/toolchain lock; original C1 Model/ProofBroker imports are reference material',
        'changes':['replace repository imports with Mathlib and the same numeral definition in namespace R6.C8',
                   'name the theorem coefficient_bound and expose a local hlt proof hole with an exact hlt wrapper',
                   'omit profiling/linter options; mathematical binders and goal retain their source spelling'],
        'interpretation':'synthetic recovery control derived from C1 C8; not an unmodified downstream obligation'})
    upper=2**18*(2**42-1)
    rhs=18446744069414584321
    assert upper<rhs
    r6.write_json(C8.path/'truth.json',{'method':'integer upper bound from g_hi.val < 2^42',
        'maximum_lhs':upper,'rhs':rhs,'strict_margin':rhs-upper,'true':True,
        'zero_witness_satisfies_hypotheses':True,
        'qualification':'arithmetic derivation, subsequently checked by the frozen Lean human proof'})


def enrich_manifest(manifest):
    origin=(C8.path/'source/C8.omega.lean').read_bytes()
    start=origin.rindex(b'  omega\n')+2
    manifest['schema_version']='r6-control-task-1'
    manifest['upstream']={'repository':'https://github.com/levineuwirth/proof-broker.git',
        'commit':BASE,'commit_date':'2026-09-07T10:11:08Z','source_file':ORIGIN,
        'line':22,'pristine_sha256':ORIGIN_HASH,'proof_byte_span':{'start':start,'end_exclusive':start+5}}
    manifest['control']={'kind':'synthetic_recovery_control','derived_source_sha256':C8.source_hash,
        'source_provenance':'source-provenance.json','derivation':'derivation.patch',
        'truth_check':'truth.json','required_recovery_route':C8.required_route,
        'required_witness_coefficients':{'hhi':'262144','neg_goal':'1'},
        'benchmark_breadth':False,
        'original_declaration_meaning':'named derived control before proof-hole instrumentation; upstream is an anonymous example'}
    files=['Capture.lean','source-provenance.json','derivation.patch','truth.json',
           *[str(p.relative_to(C8.path)) for p in sorted((C8.path/'source').iterdir())]]
    manifest['artifacts_sha256'].update({name:r6.sha(C8.path/name) for name in files})


def check_recovery(packet,route):
    if route!=C8.required_route:
        raise ValueError('C8 requires exact-support recovery')
    witness=packet['certificate']['payload']['witness_data']['coefficients']
    expected=[{'hypothesis':'hhi','coefficient':'262144'},
              {'hypothesis':'neg_goal','coefficient':'1'}]
    if sorted(witness,key=lambda x:x['hypothesis'])!=expected:
        raise ValueError('C8 witness differs from its frozen recovery requirement')
    original=r6.read_json(C8.path/'source/C8.final_ir.json')
    for part in ['goal','context']:
        if packet['final_ir'][part]!=original[part]:
            raise ValueError(f'C8 logical IR differs from C1: {part}')
