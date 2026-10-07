#!/usr/bin/env python3
"""Derive a complete index while retaining exact interrupted-run receipts."""
import copy
import hashlib
import json
from pathlib import Path
import shutil

campaign = Path(__file__).resolve().parent
output = campaign / 'profiles-after'
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):
    return json.loads(path.read_text())
def write(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
original = output / 'profiles.json'
preserved = output / 'profiles-attempt-1.json'
assert not preserved.exists(), 'Refusing to repeat aggregation'
original_bytes = original.read_bytes()
first = json.loads(original_bytes)
assert len(first) == 12 and all(r['measurement_valid'] for r in first[:11])
assert first[11]['exit_code'] != 0 and first[11]['measurement_valid'] is False
for source, dest in [('native-profile-guarded', 'native-guarded'),
                     ('profiles-after-continuation', 'continuation'),
                     ('native-profile-control', 'native-exploratory')]:
    assert (campaign / source / 'profiles.json').is_file()
    assert not (output / dest).exists()
native = read(campaign / 'native-profile-guarded/profiles.json')
continuation = read(campaign / 'profiles-after-continuation/profiles.json')
assert len(native) == 2 and all(r['trace_mode'] == 'native' for r in native)
assert len(continuation) == 3
assert all(r['exit_code'] == 0 and r['measurement_valid'] for r in native + continuation[:2])
assert continuation[2]['exit_code'] != 0 and continuation[2]['measurement_valid'] is False
preserved.write_bytes(original_bytes)
for source, dest in [('native-profile-guarded', 'native-guarded'),
                     ('profiles-after-continuation', 'continuation'),
                     ('native-profile-control', 'native-exploratory')]:
    shutil.copytree(campaign / source, output / dest)
fields = ('log', 'events', 'resources', 'setup_snapshot', 'trace_snapshot',
          'import_context', 'source_snapshot')
def canonical(row, index, position, prefix=''):
    result = copy.deepcopy(row)
    for key in fields:
        if result.get(key) and prefix:
            result[key] = prefix + '/' + result[key]
    result['receipt_origin'] = {'index': index, 'sha256': digest(output / index),
                                'record_index': position, 'input_prefix': prefix}
    return result
results = [canonical(r, preserved.name, i) for i, r in enumerate(first[:11])]
results += [canonical(native[0], 'native-guarded/profiles.json', 0, 'native-guarded')]
results += [canonical(r, 'continuation/profiles.json', i, 'continuation') for i, r in enumerate(continuation[:2])]
results += [canonical(native[1], 'native-guarded/profiles.json', 1, 'native-guarded')]
plan = read(campaign / 'after-profile-plan.json')['modules']
assert [r['module'] for r in results] == plan
exploratory = read(output / 'native-exploratory/profiles.json')[0]
attempts = {'schema': 'cloning-elaboration-profile-attempts-v1', 'attempts': [
    {'profile': first[11], 'original_index': preserved.name,
     'original_index_sha256': digest(preserved), 'original_record_index': 11,
     'input_prefix': '', 'evidence_role': 'failed-profile-attempt',
     'reason': 'Untouched module passed the full cold build, but Firefox trace collection hit its existing typeclass and elaboration heartbeat limits. No Firefox export occurred after errors. Excluded from successful cohort.',
     'expected_missing_inputs': ['events']},
    {'profile': continuation[2], 'original_index': 'continuation/profiles.json',
     'original_index_sha256': digest(output / 'continuation/profiles.json'),
     'original_record_index': 2, 'input_prefix': 'continuation',
     'evidence_role': 'failed-profile-attempt',
     'reason': 'Untouched module passed the full cold build, but Firefox trace collection hit its existing typeclass heartbeat limit. No Firefox export occurred after errors. Excluded from successful cohort.',
     'expected_missing_inputs': ['events']},
    {'profile': exploratory, 'original_index': 'native-exploratory/profiles.json',
     'original_index_sha256': digest(output / 'native-exploratory/profiles.json'),
     'original_record_index': 0, 'input_prefix': 'native-exploratory',
     'evidence_role': 'diagnostic-native-control',
     'reason': 'Exploratory native-only control passed, but setup/trace unchanged flags were inherited from the failed record, not remeasured by this driver. Excluded from canonical cohort; the fresh guarded native run is canonical.',
     'expected_missing_inputs': []}]}
write(output / 'profile-attempts.json', attempts)
write(output / 'aggregation.json', {'schema': 'cloning-elaboration-profile-aggregation-v1',
    'driver_sha256': digest(Path(__file__)), 'plan_sha256': digest(campaign / 'after-profile-plan.json'),
    'preserved_interrupted_index_sha256': digest(preserved),
    'profile_count': len(results), 'notes': [
        'Canonical index is derived; every row is bound to an exact preserved original index.',
        'Only evidence input filenames are rebased; native commands and measurements are unchanged.',
        'Failed and exploratory attempts are preserved separately and excluded from canonical success.']})
write(original, results)
print(json.dumps({'canonical_successes': len(results), 'separate_attempts': len(attempts['attempts'])}))
