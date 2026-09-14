"""R6-010 census: every textual `omega` site of the frozen source, classified, with a stable identity per site.

The census is derived from the retained pristine bytes of `Bracket.lean` at the pinned upstream commit, never from a live
checkout. A site is an `omega` token outside comments and string literals; its identity is the byte span of that token,
not the text of its line (bare `omega` lines repeat verbatim). Each site carries its containing declaration (the family
unit), a syntactic form, an exposure record (whether its obligation was ever model-visible in an earlier checkpoint), a
task id and the name of the saved local declaration its capture will add. Admission or exclusion is decided by the
capture and freeze in `site_freeze.py`, never here: this module only lists and classifies.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
PRISTINE = ROOT/'tasks/verinf-d1-70/Pristine.lean'
SOURCE_HASH = '03b4d5ca39f435b0eed7d79fe70e9cc33c401fc7ec240a4120a194b54de722a2'
UPSTREAM = {'repository': 'https://github.com/JamesPetrie/VerInf.git', 'commit': 'c07e03c94884e9084ffaf7a7294fc0907672f6c2',
            'commit_date': '2026-07-21T22:25:27Z', 'source_file': 'lean/BracketSpike/BracketSpike/Bracket.lean'}
CENSUS_ID = 'bracket-c07e03c9'
SCHEMA = 'r6-census-1'
TOKEN = b'omega'
DECLARATION = re.compile(r'^(?:private |protected |noncomputable )*(lemma|theorem|def|instance|structure|abbrev)\s+([A-Za-z_][\w.\']*)')
FORMS = (('have_post_simp', re.compile(r'^\s*(?:·\s*)?have\s+[A-Za-z_][\w\']*\s*:.*:=\s*by\s+simp\b.*;\s*omega\s*$')),
         ('named_have', re.compile(r'^\s*(?:·\s*)?have\s+[A-Za-z_][\w\']*\s*:.*:=\s*by\s+omega\s*$')),
         ('anonymous_have', re.compile(r'^\s*(?:·\s*)?have\s*:.*:=\s*by\s+omega\s*$')),
         ('post_simp', re.compile(r'^\s*(?:·\s*)?simp\b.*;\s*omega\s*$')),
         ('bare_goal', re.compile(r'^\s*(?:·\s*)?omega\s*$')),
         ('inline_term', re.compile(r'^.*\(by\s+omega\).*$')),
         ('term_by', re.compile(r'^.*:=\s*by\s+omega\s*$')))
# What earlier checkpoints made model-visible. Line 70 is the R6-000 control `verinf-d1-70`, whose obligation was sent to the
# provider by every live checkpoint; no other site of this file has been extracted or transmitted before this census.
EXPOSURE = {70: {'exposed': True, 'as_task': 'verinf-d1-70', 'model_visible_in': ['R6-007 live-2 (pilot-runs/live-2)', 'R6-008 v7 live-1 (campaign-runs-v7/live-1)'],
                 'scope': 'the obligation, its rows and the deterministic first-hit witness were model-visible; the analysis must stratify on this'}}
# The frozen expectation: extraction from the pinned bytes must reproduce exactly these (line, column, declaration, form).
EXPECTED_SITES = ((69, 55, 'Bracket.lift_cell', 'named_have'), (70, 45, 'Bracket.lift_cell', 'named_have'), (71, 4, 'Bracket.lift_cell', 'bare_goal'),
                  (78, 48, 'Bracket.lift_cell', 'term_by'), (96, 32, 'Bracket.threshold_unique', 'named_have'), (98, 4, 'Bracket.threshold_unique', 'bare_goal'),
                  (99, 32, 'Bracket.threshold_unique', 'named_have'), (101, 4, 'Bracket.threshold_unique', 'bare_goal'),
                  (158, 41, 'Bracket.cell_value_neutral', 'have_post_simp'), (166, 31, 'Bracket.cell_value_neutral', 'inline_term'),
                  (170, 32, 'Bracket.cell_value_neutral', 'named_have'), (175, 20, 'Bracket.cell_value_neutral', 'post_simp'),
                  (178, 6, 'Bracket.cell_value_neutral', 'bare_goal'), (180, 32, 'Bracket.cell_value_neutral', 'anonymous_have'),
                  (204, 52, 'Bracket.Row.s1_noninc', 'inline_term'))


def sha(data): return hashlib.sha256(data).hexdigest()


def pristine():
    data = PRISTINE.read_bytes()
    if sha(data) != SOURCE_HASH: raise ValueError('Pristine source hash mismatch')
    return data


def code_mask(data):
    """True for every byte that is code: block comments (nested), line comments and string literals are masked out."""
    mask = bytearray(b'\x01'*len(data)); i = 0; n = len(data); depth = 0
    while i < n:
        if depth:
            if data.startswith(b'/-', i): depth += 1; mask[i] = mask[i+1] = 0; i += 2; continue
            if data.startswith(b'-/', i): depth -= 1; mask[i] = mask[i+1] = 0; i += 2; continue
            mask[i] = 0; i += 1; continue
        if data.startswith(b'/-', i): depth = 1; mask[i] = mask[i+1] = 0; i += 2; continue
        if data.startswith(b'--', i):
            while i < n and data[i] != 0x0a: mask[i] = 0; i += 1
            continue
        if data[i] == 0x22:  # a string literal
            mask[i] = 0; i += 1
            while i < n and data[i] != 0x22:
                if data[i] == 0x5c: mask[i] = 0; i += 1
                if i < n: mask[i] = 0; i += 1
            if i < n: mask[i] = 0; i += 1
            continue
        i += 1
    if depth: raise ValueError('unterminated block comment')
    return bytes(mask)


def declarations(data):
    """Column-zero declaration headers with their namespace prefix, as (byte offset, full name)."""
    found = []; stack = []; offset = 0
    for line in data.split(b'\n'):
        text = line.decode()
        if text.startswith('namespace '): stack.append(text.split()[1])
        elif text.startswith('end ') and stack and text.split()[1] == stack[-1]: stack.pop()
        m = DECLARATION.match(text)
        if m and m.group(1) != 'instance':
            found.append((offset, '.'.join([*stack, m.group(2)]), m.group(1)))
        offset += len(line)+1
    return found


def extract(data=None):
    """Every `omega` token in code position, with line, column, byte span, containing declaration and syntactic form."""
    data = pristine() if data is None else data; mask = code_mask(data); heads = declarations(data)
    lines = data.split(b'\n'); starts = []; offset = 0
    for line in lines: starts.append(offset); offset += len(line)+1
    sites = []
    for m in re.finditer(rb'(?<![A-Za-z0-9_.\'])omega(?![A-Za-z0-9_\'])', data):
        s, e = m.span()
        if not all(mask[s:e]): continue
        line_index = max(i for i, st in enumerate(starts) if st <= s); text = lines[line_index].decode()
        column = len(data[starts[line_index]:s].decode())
        containing = [h for h in heads if h[0] <= s]
        if not containing: raise ValueError(f'omega at line {line_index+1} precedes every declaration')
        _, declaration, keyword = containing[-1]
        form = next((name for name, pattern in FORMS if pattern.match(text)), 'unclassified')
        sites.append({'line': line_index+1, 'column': column, 'byte_span': {'start': s, 'end_exclusive': e}, 'declaration': declaration,
                      'declaration_keyword': keyword, 'form': form, 'line_text': text})
    return sites


def site_id(line): return f'bracket-l{line:03d}'
def saved_name(declaration, line): return f'{declaration}.r6_site_l{line:03d}'


def census(data=None):
    """The complete, frozen census record: extraction must reproduce the expected population exactly."""
    data = pristine() if data is None else data; sites = extract(data)
    observed = tuple((s['line'], s['column'], s['declaration'], s['form']) for s in sites)
    if observed != EXPECTED_SITES: raise ValueError(f'census population changed: {observed}')
    families = {}
    for s in sites: families.setdefault(s['declaration'], []).append(s['line'])
    entries = []
    for s in sites:
        entries.append({**s, 'site_id': site_id(s['line']), 'saved_local_declaration': saved_name(s['declaration'], s['line']),
                        'family': s['declaration'], 'exposure': EXPOSURE.get(s['line'], {'exposed': False, 'as_task': None, 'model_visible_in': []})})
    return {'schema_version': SCHEMA, 'census_id': CENSUS_ID, 'upstream': UPSTREAM, 'pristine_sha256': SOURCE_HASH, 'token': TOKEN.decode(),
            'site_count': len(entries), 'families': families, 'sites': entries,
            'scope': 'textual omega sites of one file at one commit; a site is not an admitted or independent task until its capture and freeze succeed'}


LOCK = ROOT/'policies/census-harness-v1.sha256.json'
FILES = ('census.py', 'site_freeze.py', 'test_census.py', 'capture/CaptureSite.lean', 'schema/task-site.schema.json')


def lock():
    """The source lock of the census harness: written once, after the freeze and its controls; any later edit is a new revision."""
    if LOCK.exists(): raise ValueError('census lock already exists')
    LOCK.write_text(json.dumps({p: sha((ROOT/p).read_bytes()) for p in FILES}, indent=2)+'\n')
    return LOCK


def verify_lock():
    values = json.loads(LOCK.read_bytes())
    if set(values) != set(FILES): raise ValueError('census source inventory changed')
    if any(sha((ROOT/p).read_bytes()) != h for p, h in values.items()): raise ValueError('census harness requires its frozen source revision')
    return values


def membership(census_dir):
    """The proposed primary membership: every admitted site, with exposure flagged and every exclusion carried with its reason,
    hash-bound to the frozen census and to each site manifest. Membership is frozen by review before either arm runs."""
    frozen = json.loads((census_dir/'census.json').read_bytes()); by_id = {s['site_id']: s for s in frozen['sites']}
    primary = list(frozen['admitted'])
    excluded = {r['site_id']: r['reason'] for r in frozen['results'] if r['status'] != 'admitted'}
    return {'schema_version': 'r6-census-membership-1', 'census_id': frozen['census_id'], 'census_sha256': sha((census_dir/'census.json').read_bytes()),
            'pristine_sha256': frozen['pristine_sha256'], 'primary': primary, 'excluded': excluded,
            'exposed': [s for s in primary if by_id[s]['exposure']['exposed']],
            'families': {f: [s for s in primary if by_id[s]['declaration'] == f] for f in frozen['families']},
            'manifests_sha256': {s: sha((census_dir/s/'manifest.json').read_bytes()) for s in primary},
            'status': 'proposed; frozen by review approval before the deterministic arm or any learned draw',
            'scope': 'one file at one commit; eight draws per primary site do not add independent families; the exposed site is stratified, not removed'}


if __name__ == '__main__':
    import sys
    if sys.argv[1:2] == ['lock']: print(lock())
    elif sys.argv[1:2] == ['membership']:
        directory = ROOT/'tasks/census-v1'; target = directory/'membership.json'
        if target.exists(): raise SystemExit('membership already recorded: '+str(target))
        target.write_bytes(json.dumps(membership(directory), indent=2, sort_keys=True).encode()+b'\n'); print(target)
    else: print(json.dumps(census(), indent=1))
