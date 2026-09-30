#!/usr/bin/env python3
"""Audit the kernel axiom dependencies of every compiled project declaration.

Run after `python3 check_local.py`. Uses the same optional environment overrides.
The generated Audit.lean is also checkable with `lake env lean Audit.lean`.
`--generate-only` writes that driver without running Lean.
`--resummarize` reuses an existing completed audit after validating its provenance.
`--jobs N` optionally audits disjoint module-index partitions in parallel. Every
worker imports the same full project; Audit.lean remains the serial master.

Source parsing supplies descriptive theorem counts and a placeholder check only.
Audit coverage comes from Lean's imported-module constant tables, so private
declarations, attributed/protected theorems, definitions, instances, and generated
helpers are all included without guessing their elaborated names.
"""
from pathlib import Path
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import argparse, hashlib, json, os, re, subprocess, sys

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
mode = parser.add_mutually_exclusive_group()
mode.add_argument('--generate-only', action='store_true')
mode.add_argument('--resummarize', action='store_true')
parser.add_argument('--jobs', type=int, default=1,
                    help='parallel Lean workers for a fresh audit (default: 1)')
args = parser.parse_args()
if args.jobs < 1:
    parser.error('--jobs must be a positive integer')
def source_tokens(text):
    """Mask nested comments and strings, preserving newlines for diagnostics."""
    out, depth, pos, string = [], 0, 0, False
    while pos < len(text):
        pair = text[pos:pos + 2]
        if string:
            if text[pos] == '\\' and pos + 1 < len(text):
                out.extend('  ')
                pos += 2
                continue
            if text[pos] == '"':
                string = False
            out.append('\n' if text[pos] == '\n' else ' ')
            pos += 1
        elif pair == '/-':
            depth += 1
            out.extend('  ')
            pos += 2
        elif depth and pair == '-/':
            depth -= 1
            out.extend('  ')
            pos += 2
        elif not depth and pair == '--':
            end = text.find('\n', pos)
            out.extend(' ' * ((len(text) if end < 0 else end) - pos))
            pos = len(text) if end < 0 else end
        elif not depth and text[pos] == '"':
            string = True
            out.append(' ')
            pos += 1
        else:
            out.append(text[pos] if not depth or text[pos] == '\n' else ' ')
            pos += 1
    return ''.join(out)

files = sorted((root / 'Cloning').rglob('*.lean'))
counts, source_declarations = {}, []
declaration_pattern = re.compile(
    r'^\s*(?:@\[[^\n]*\]\s*)*'
    r'(?:(?:private|protected|noncomputable|unsafe)\s+)*'
    r'(theorem|lemma)\s+(\S+)', re.M)
for file in files:
    checked_source = source_tokens(file.read_text())
    if re.search(r'\b(?:sorry|admit|axiom|sorryAx)\b', checked_source):
        raise SystemExit('Unproved declaration or placeholder in ' + str(file))
    matches = list(declaration_pattern.finditer(checked_source))
    relative = str(file.relative_to(root / 'Cloning'))
    counts[relative] = len(matches)
    source_declarations.extend({
        'file': str(file.relative_to(root)),
        'kind': match.group(1),
        'written_name': match.group(2),
        'line': checked_source.count('\n', 0, match.start(1)) + 1,
    } for match in matches)

driver = '''import Cloning
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    if modName == `Cloning || (`Cloning).isPrefixOf modName then
      let data := env.header.moduleData[idx]!
      liftIO <| IO.println ("MODULE_REPORT " ++ modName.toString)
      for name in data.constNames do
        let some info := env.find? name
          | throwError "Missing compiled declaration {name} from {modName}"
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let axioms ← collectAxioms name
        let report := Json.mkObj [
          ("module", toJson modName.toString),
          ("name", toJson name.toString),
          ("kind", toJson kind),
          ("private", toJson (name.toString.startsWith "_private.")),
          ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString))]
        liftIO <| IO.println ("AXIOM_REPORT " ++ report.compress)
        let allowed := #["propext", "Classical.choice", "Quot.sound"]
        let unexpected := axioms.filter (fun a => !allowed.contains a.toString)
        unless unexpected.isEmpty do
          throwError "Unexpected axioms in {name}: {unexpected}"
'''
def sha256(data):
    return hashlib.sha256(data).hexdigest()

def shard_driver(jobs, index):
    """Keep the exact master audit body; partition only its outer module loop."""
    condition = 'modName == `Cloning || (`Cloning).isPrefixOf modName'
    original = '    if ' + condition + ' then\n'
    inventory = '''    if CONDITION then
      let data := env.header.moduleData[idx]!
      let inventory := Json.mkObj [
        ("module", toJson modName.toString),
        ("index", toJson idx),
        ("owner", toJson (idx % JOBS)),
        ("constant_names", toJson (data.constNames.map Name.toString))]
      liftIO <| IO.println ("SHARD_INVENTORY " ++ inventory.compress)
    if (CONDITION) && idx % JOBS == INDEX then
'''.replace('CONDITION', condition).replace('JOBS', str(jobs)).replace('INDEX', str(index))
    if driver.count(original) != 1:
        raise RuntimeError('Master module filter is not uniquely identifiable')
    result = driver.replace(original, inventory, 1)
    result += ('  liftIO <| IO.println ("SHARD_COMPLETE " ++ '
               f'(Json.mkObj [("index", toJson ({index} : Nat)), '
               f'("jobs", toJson ({jobs} : Nat))]).compress)\n')
    return result

def shard_paths(jobs, index):
    stem = f'audit-shards/Shard{index:03d}-of-{jobs:03d}'
    return stem + '.lean', stem + '.txt'

def parse_output(output):
    reports, modules, inventory, completed = [], [], [], []
    for line in output.splitlines():
        if line.startswith('MODULE_REPORT '):
            modules.append(line.removeprefix('MODULE_REPORT ').strip())
        elif line.startswith('AXIOM_REPORT '):
            reports.append(json.loads(line.removeprefix('AXIOM_REPORT ')))
        elif line.startswith('SHARD_INVENTORY '):
            inventory.append(json.loads(line.removeprefix('SHARD_INVENTORY ')))
        elif line.startswith('SHARD_COMPLETE '):
            completed.append(json.loads(line.removeprefix('SHARD_COMPLETE ')))
    return reports, modules, inventory, completed

def validate_shards(records, jobs, expected_modules):
    """Validate exact exported-name coverage and identical imported environments.

    Every worker supplies the complete module/name inventory, but reports axioms
    only for its assigned module indices. Counters retain duplicate exports.
    """
    if len(records) != jobs or sorted(r['index'] for r in records) != list(range(jobs)):
        raise SystemExit('Missing or repeated audit shard')
    reference = None
    outputs = []
    for record in sorted(records, key=lambda r: r['index']):
        index = record['index']
        if record.get('jobs') != jobs or record.get('lean_exit_code') != 0:
            raise SystemExit(f'Audit shard {index} did not complete successfully')
        driver_path, output_path = shard_paths(jobs, index)
        if record.get('driver_path') != driver_path or record.get('output_path') != output_path:
            raise SystemExit(f'Unexpected artifact paths for audit shard {index}')
        source = (root / driver_path).read_text()
        output = (root / output_path).read_text()
        if (source != shard_driver(jobs, index) or
                sha256(source.encode()) != record.get('driver_sha256') or
                sha256(output.encode()) != record.get('output_sha256')):
            raise SystemExit(f'Fingerprint mismatch for audit shard {index}')
        reports, modules, inventory, completed = parse_output(output)
        if completed != [{'index': index, 'jobs': jobs}]:
            raise SystemExit(f'Missing or repeated completion marker for audit shard {index}')
        if reference is None:
            reference = inventory
            names = [entry['module'] for entry in inventory]
            indices = [entry['index'] for entry in inventory]
            if (len(names) != len(set(names)) or len(indices) != len(set(indices)) or
                    set(names) != expected_modules | {'Cloning'}):
                raise SystemExit('Full imported project inventory does not match source modules')
            if any(entry['owner'] != entry['index'] % jobs for entry in inventory):
                raise SystemExit('Invalid module-index partition in audit inventory')
        elif inventory != reference:
            raise SystemExit('Audit workers loaded different module/name inventories')
        assigned = [entry for entry in inventory if entry['owner'] == index]
        if Counter(modules) != Counter(entry['module'] for entry in assigned):
            raise SystemExit(f'Incorrect module coverage in audit shard {index}')
        wanted = Counter((entry['module'], name) for entry in assigned
                         for name in entry['constant_names'])
        actual = Counter((report['module'], report['name']) for report in reports)
        if actual != wanted:
            raise SystemExit(f'Incorrect constant export coverage in audit shard {index}')
        if record.get('constant_reports') != len(reports):
            raise SystemExit(f'Incorrect report count for audit shard {index}')
        outputs.append(output)
    return ''.join(outputs)

def run_lean(lean, env, source_path, label=''):
    process = subprocess.Popen([lean, '-DautoImplicit=false', source_path],
        cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    lines, progress = [], 0
    for line in process.stdout:
        lines.append(line)
        if line.startswith('AXIOM_REPORT '):
            progress += 1
            if progress % 100 == 0:
                print(f'{label}AXIOM REPORTS {progress} compiled constant exports', flush=True)
    return process.wait(), ''.join(lines)

def classify(reports):
    result = {}
    for report in reports:
        kind = report['kind']
        result[kind] = result.get(kind, 0) + 1
    return result

def aggregate_reports(reports):
    """Names identify kernel declarations; module export tables may overlap.

    Generated congruence lemmas can occur in several module constNames tables.
    Every occurrence was audited against the same environment. Ignore only its
    export location when checking that repetitions give identical information.
    """
    unique, export_modules, conflicts, raw_by_module = {}, {}, {}, {}
    for report in reports:
        name, module = report['name'], report['module']
        normalized = {key: value for key, value in report.items() if key != 'module'}
        normalized['axioms'] = sorted(set(normalized['axioms']))
        raw_by_module[module] = raw_by_module.get(module, 0) + 1
        export_modules.setdefault(name, []).append(module)
        if name in unique and unique[name] != normalized:
            conflicts.setdefault(name, [unique[name]]).append(normalized)
        else:
            unique.setdefault(name, normalized)
    repeated = {name: modules for name, modules in export_modules.items() if len(modules) > 1}
    return unique, repeated, conflicts, raw_by_module

source_sha256 = {str(file.relative_to(root)): sha256(file.read_bytes())
                 for file in [root / 'Cloning.lean'] + files}
driver_sha256 = sha256(driver.encode())
expected_modules = {'.'.join(file.relative_to(root).with_suffix('').parts) for file in files}
audit_jobs, shard_records = args.jobs, []
if args.resummarize:
    # The old script wrote verification.json only after Lean returned zero.
    # Require that completion artifact and its agreement with the raw output;
    # never accept an arbitrary/incomplete AXIOMS.txt merely for looking plausible.
    previous = json.loads((root / 'verification.json').read_text())
    output = (root / 'AXIOMS.txt').read_text()
    if (root / 'Audit.lean').read_text() != driver:
        raise SystemExit('Existing audit driver differs; run a fresh audit')
    if previous.get('lean_exit_code', 0) != 0:
        raise SystemExit('Existing audit does not record successful Lean completion')
    if (previous.get('source_placeholder_scan') != 'passed' or
            previous.get('by_module') != counts or
            previous.get('source_declarations') != source_declarations):
        raise SystemExit('Existing completion summary does not match current source declarations')
    for key, value in [('audit_output_sha256', sha256(output.encode())),
                       ('audit_driver_sha256', driver_sha256),
                       ('source_sha256', source_sha256)]:
        if key in previous and previous[key] != value:
            raise SystemExit('Existing audit fingerprint mismatch: ' + key)
    audit_jobs = previous.get('audit_jobs', 1)
    shard_records = previous.get('audit_shards', [])
    if audit_jobs > 1:
        if output != validate_shards(shard_records, audit_jobs, expected_modules):
            raise SystemExit('Combined output differs from the completed audit shards')
    elif audit_jobs != 1 or shard_records:
        raise SystemExit('Invalid existing audit worker provenance')
    completion_basis = previous.get('lean_completion_basis',
        'legacy verification.json was written only after Lean returned zero; '
        'raw counts, classifications, module coverage, and source declarations matched on migration')
else:
    (root / 'Audit.lean').write_text(driver)
    if audit_jobs > 1:
        (root / 'audit-shards').mkdir(exist_ok=True)
        for index in range(audit_jobs):
            driver_path, _ = shard_paths(audit_jobs, index)
            (root / driver_path).write_text(shard_driver(audit_jobs, index))
    if args.generate_only:
        print(f'Generated Audit.lean; {sum(counts.values())} source theorems in {len(files)} modules; '
              f'{audit_jobs} audit worker(s)')
        sys.exit(0)
    lean = os.environ.get('CLONING_LEAN', '/Users/jw/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean')
    packages = Path(os.environ.get('CLONING_PACKAGES', '/Users/jw/Downloads/continuity-of-regularized-channel-renyi-divergence/.lake/packages'))
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(root / 'build'), str(root)] +
        [str(p) for p in packages.glob('*/.lake/build/lib/lean')])
    if audit_jobs == 1:
        returncode, output = run_lean(lean, env, 'Audit.lean')
        (root / 'AXIOMS.txt').write_text(output)
        if returncode:
            print(output)
            sys.exit(returncode)
        completion_basis = 'Lean subprocess returned zero in this audit run'
    else:
        def run_shard(index):
            driver_path, output_path = shard_paths(audit_jobs, index)
            print(f'AUDIT SHARD {index + 1}/{audit_jobs} started', flush=True)
            code, result = run_lean(lean, env, driver_path, f'SHARD {index + 1}: ')
            (root / output_path).write_text(result)
            reports, _, _, _ = parse_output(result)
            record = {'index': index, 'jobs': audit_jobs,
                      'driver_path': driver_path,
                      'driver_sha256': sha256((root / driver_path).read_bytes()),
                      'output_path': output_path, 'output_sha256': sha256(result.encode()),
                      'lean_exit_code': code, 'constant_reports': len(reports)}
            print(f'AUDIT SHARD {index + 1}/{audit_jobs} completed with exit {code}', flush=True)
            return record
        with ThreadPoolExecutor(max_workers=audit_jobs) as executor:
            shard_records = list(executor.map(run_shard, range(audit_jobs)))
        output = ''.join((root / r['output_path']).read_text() for r in shard_records)
        (root / 'AXIOMS.txt').write_text(output)
        failed_shards = [r for r in shard_records if r['lean_exit_code'] != 0]
        if failed_shards:
            for record in failed_shards:
                print(f"Lean audit failed in {record['driver_path']}; see {record['output_path']}")
            sys.exit(1)
        if validate_shards(shard_records, audit_jobs, expected_modules) != output:
            raise SystemExit('Combined audit output differs from shard artifacts')
        completion_basis = (f'All {audit_jobs} full-environment Lean shard subprocesses returned zero; '
                            'identical inventories and exact disjoint export coverage verified')

reports, module_reports, _, _ = parse_output(output)
reported_modules = set(module_reports)
unique, repeated, conflicts, raw_by_module = aggregate_reports(reports)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
unexpected = {axiom for report in reports for axiom in report['axioms']} - allowed
missing_modules = sorted(expected_modules - reported_modules)
if args.resummarize:
    previous_count = previous.get('raw_constant_reports', previous.get('audited_constants'))
    previous_classification = previous.get('raw_constant_classification', previous.get('constant_classification'))
    if (previous_count != len(reports) or previous_classification != classify(reports) or
            previous.get('compiled_constants_by_module') != raw_by_module or
            previous.get('missing_modules') != missing_modules or
            previous.get('unexpected_axioms') != sorted(unexpected)):
        raise SystemExit('Existing completion summary does not match raw audit output')
failed = bool(unexpected or missing_modules or conflicts or not reports)
summary = {'theorems': sum(counts.values()), 'modules': len(counts), 'by_module': counts,
           'theorem_count_basis': 'source-declared theorem/lemma commands, including attributes and modifiers',
           'source_declarations': source_declarations,
           'audited_constants': len(unique),
           'constant_count_basis': 'unique kernel declaration names; identical repeated module exports counted once',
           'constant_classification': classify(unique.values()),
           'raw_constant_reports': len(reports),
           'raw_constant_classification': classify(reports),
           'compiled_constants_by_module': raw_by_module,
           'compiled_constants_by_module_basis': 'module export occurrences, before deduplication',
           'private_constants': sum(report['private'] for report in unique.values()),
           'audit_coverage': 'all constant names in every imported Cloning module, via Lean environment tables',
           'allowed_axioms': sorted(allowed), 'unexpected_axioms': sorted(unexpected),
           'missing_reports': missing_modules, 'missing_modules': missing_modules,
           'duplicate_reports': sorted(conflicts),
           'repeated_export_names': repeated, 'conflicting_reports': conflicts,
           'lean_exit_code': 0, 'lean_completion_basis': completion_basis,
           'audit_jobs': audit_jobs, 'audit_shards': shard_records,
           'audit_partition': ('serial master' if audit_jobs == 1 else
               'full imported module index modulo audit_jobs; same full Cloning environment in every worker'),
           'audit_output_sha256': sha256(output.encode()),
           'audit_driver_sha256': driver_sha256, 'source_sha256': source_sha256,
           'source_placeholder_scan': 'passed',
           'axiom_audit': 'failed' if failed else 'passed'}
(root / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
if failed:
    sys.exit(1)
