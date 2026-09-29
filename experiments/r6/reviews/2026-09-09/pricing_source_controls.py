#!/usr/bin/env python3
"""One-relationship controls for the R6-005 closeout's offline source utility."""
import argparse
import copy
import json
from pathlib import Path
import shutil
import tempfile

import pricing_sources as p

CASES = (
    'captured_sources', 'sol_policy_reservation', 'raw_mutation_rejected',
    'rehashed_false_extract_rejected', 'missing_page_rejected',
    'changed_output_rate_detected', 'changed_cache_multiplier_detected',
    'changed_pricing_condition_detected', 'changed_dated_id_detected',
    'raw_change_without_extract_change', 'missing_pricing_section_rejected',
    'wrong_extractor_digest_rejected',
)


def overwrite(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False)+'\n')


def rebind(bundle, model, *, reextract=True):
    raw_path = bundle/(model+'.html')
    derived_path = bundle/(model+'.extract.json')
    receipt_path = bundle/(model+'.receipt.json')
    raw = raw_path.read_bytes()
    if reextract:
        overwrite(derived_path, p.extract(raw, model))
    derived = json.loads(derived_path.read_bytes())
    receipt = json.loads(receipt_path.read_bytes())
    receipt['raw'] = {'file': raw_path.name, 'bytes': len(raw), 'sha256': p.sha(raw)}
    receipt['transfer']['download_bytes'] = len(raw)
    receipt['extract'] = {'file': derived_path.name, 'bytes': derived_path.stat().st_size,
                          'sha256': p.sha(derived_path.read_bytes()), 'canonical_sha256': p.sha(p.canonical(derived))}
    overwrite(receipt_path, receipt)


def run(bundle, policy, output):
    checks = []
    p.write(output, {'passed': False, 'checks': []})

    def record(name, detail):
        checks.append({'name': name, 'passed': True, 'detail': detail})
        overwrite(output, {'passed': False, 'checks': checks})

    def baseline(path):
        for model in p.MODELS:
            p.verify(path, model)
        return p.policy_check(path, policy)

    def reject(action, message):
        try:
            action()
        except (ValueError, FileNotFoundError) as exc:
            p.require(message in str(exc), 'unexpected rejection: '+str(exc))
            return str(exc)
        raise AssertionError('corruption was accepted: '+message)

    def replace_once(path, old, new):
        raw = path.read_bytes()
        p.require(raw.count(old) == 1, 'mutation precondition is not exactly one match')
        path.write_bytes(raw.replace(old, new))

    baseline(bundle)
    sol, _ = p.verify(bundle, 'gpt-5.6-sol')
    dated, _ = p.verify(bundle, 'gpt-5.4')
    p.require(sol['listed_dated_ids'] == [] and dated['listed_dated_ids'] == ['gpt-5.4-2026-03-05'], 'snapshot observation differs')
    p.require(dated['per_million_tokens']['cache_write'] is None, 'missing cache-write rate became a number')
    record('captured_sources', {'sources': 2, 'sol_dated_ids': [], 'gpt54_dated_ids': dated['listed_dated_ids'],
                               'gpt54_cache_write': None})
    calculated = p.policy_check(bundle, policy)
    p.require(calculated['reservation_micro_usd'] == 163840, 'reservation differs')
    unchanged = p.compare(bundle, bundle, 'gpt-5.6-sol')
    p.require(not unchanged['raw_changed'] and unchanged['changed_fields'] == [], 'unchanged refresh differs')
    record('sol_policy_reservation', calculated)

    for name in CASES[2:]:
        with tempfile.TemporaryDirectory(prefix='r6-pricing-control-') as tmp:
            altered = Path(tmp)/'sources'
            shutil.copytree(bundle, altered)
            baseline(altered)
            detail = {'unmutated_copy_passes': True, 'changed_relationships': 1}
            model = 'gpt-5.6-sol'
            raw_path = altered/(model+'.html')
            if name == 'raw_mutation_rejected':
                raw_path.write_bytes(raw_path.read_bytes()+b'\n')
                detail['rejection'] = reject(lambda: p.verify(altered, model), 'raw source binding differs')
            elif name == 'rehashed_false_extract_rejected':
                derived_path = altered/(model+'.extract.json')
                derived = json.loads(derived_path.read_bytes())
                derived['per_million_tokens']['output'] = '21.00'
                overwrite(derived_path, derived)
                rebind(altered, model, reextract=False)
                detail['rejection'] = reject(lambda: p.verify(altered, model), 'pricing extraction differs from retained page')
            elif name == 'missing_page_rejected':
                raw_path.unlink()
                detail['rejection'] = reject(lambda: p.verify(altered, model), '.html')
            elif name in ('changed_output_rate_detected', 'changed_cache_multiplier_detected', 'changed_pricing_condition_detected'):
                old, new = {
                    'changed_output_rate_detected': (b'>$20.00<', b'>$21.00<'),
                    'changed_cache_multiplier_detected': (b'Cache writes are billed at 1.25x', b'Cache writes are billed at 1.50x'),
                    'changed_pricing_condition_detected': (b'November 21, 2026', b'November 22, 2026'),
                }[name]
                replace_once(raw_path, old, new)
                rebind(altered, model)
                comparison = p.compare(bundle, altered, model)
                p.require(comparison['raw_changed'] and comparison['extract_changed'] and comparison['pricing_text_changed'], 'source change went undetected')
                p.require(comparison['rates_changed'] == (name != 'changed_pricing_condition_detected'), 'numeric/text distinction differs')
                detail['comparison'] = comparison
                if name != 'changed_pricing_condition_detected':
                    detail['policy_rejection'] = reject(lambda: p.policy_check(altered, policy), 'policy rates differ from source')
                else:
                    # Matching numbers alone cannot approve changed pricing conditions.
                    detail['numeric_policy_comparison_still_passes'] = p.policy_check(altered, policy)['rates_match']
                    p.require(comparison['automatic_live_authorization'] is False, 'diff authorized a live call')
            elif name == 'changed_dated_id_detected':
                model = 'gpt-5.4'
                path = altered/(model+'.html')
                raw = path.read_bytes()
                occurrences = raw.count(b'gpt-5.4-2026-03-05')
                p.require(occurrences > 0, 'dated-id mutation has no target')
                path.write_bytes(raw.replace(b'gpt-5.4-2026-03-05', b'gpt-5.4-2026-03-06'))
                rebind(altered, model)
                comparison = p.compare(bundle, altered, model)
                p.require(comparison['snapshot_ids_changed'] and not comparison['rates_changed'], 'snapshot/rate distinction differs')
                detail.update(comparison=comparison, replaced_occurrences=occurrences)
            elif name == 'raw_change_without_extract_change':
                raw_path.write_bytes(raw_path.read_bytes()+b'\n<!-- synthetic closeout control -->\n')
                rebind(altered, model)
                comparison = p.compare(bundle, altered, model)
                p.require(comparison['raw_changed'] and not comparison['extract_changed'] and not comparison['automatic_live_authorization'], 'raw/extract distinction differs')
                detail['comparison'] = comparison
            elif name == 'missing_pricing_section_rejected':
                replace_once(raw_path, b'Text tokens', b'Renamed tokens')
                detail['rejection'] = reject(lambda: p.extract(raw_path.read_bytes(), model), 'missing or ambiguous Text tokens section')
            elif name == 'wrong_extractor_digest_rejected':
                receipt_path = altered/(model+'.receipt.json')
                receipt = json.loads(receipt_path.read_bytes())
                receipt['extractor_sha256'] = '0'*64
                overwrite(receipt_path, receipt)
                detail['rejection'] = reject(lambda: p.verify(altered, model), 'extractor source binding differs')
            else:
                raise AssertionError('unhandled frozen case')
            record(name, detail)
    names = [row['name'] for row in checks]
    p.require(len(names) == len(set(names)) and set(names) == set(CASES), 'control case population differs')
    result = {'passed': True, 'check_count': len(CASES), 'expected_cases': list(CASES), 'checks': checks,
              'program_sha256': p.sha(Path(__file__).read_bytes()),
              'extractor_sha256': p.sha(Path(p.__file__).read_bytes()),
              'scope': 'offline source-provenance and comparison controls; separate from the frozen 96-check checkpoint; no native episode or live admission test'}
    overwrite(output, result)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, required=True)
    parser.add_argument('--policy', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.bundle, args.policy, args.output)
    print(json.dumps({'passed': result['passed'], 'checks': result['check_count']}))
