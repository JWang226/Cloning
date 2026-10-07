#!/usr/bin/env python3
"""Render the final comparison only from a completed public evidence bundle.

No Lean, traces, gzip, or source archives are read. The explicit --final option,
completed summaries/profile receipts, and published bundle manifest form the gate.
Use the prepared ignored notes while the after measurements remain in progress.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re

from comparison_support import finite, intervention, snapshot_comparison, validate_summary


def require(value, message):
    if not value:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def number(value, digits=2):
    return '—' if value is None else f'{value:,.{digits}f}'


def table(headers, rows):
    return '\n'.join(['| ' + ' | '.join(headers) + ' |', '| ' + ' | '.join(['---'] * len(headers)) + ' |',
                      *['| ' + ' | '.join(str(v).replace('|', r'\|').replace('\n', ' ') for v in row) + ' |' for row in rows]])


def profile_mode(profile):
    # The original Firefox records predate explicit trace_mode.
    mode = profile.get('trace_mode', 'firefox')
    require(mode in {'firefox', 'native'}, 'Unexpected profile trace mode')
    if mode == 'native':
        require(profile.get('events') is None, 'Native control must not claim Firefox output')
        require(not any(str(flag).startswith('-Dtrace.profiler') for flag in profile.get('command', [])),
                'Native command retains Firefox trace flags')
    return mode


def profile_rows(bundle, stage):
    rows = read(bundle / ('profiles-' + stage) / 'summary.json')['profiles']
    require(len({row['profile']['module'] for row in rows}) == len(rows), 'Duplicate canonical profile module')
    return {row['profile']['module']: row for row in rows}


def native_metrics(row):
    """Use native process resources already parsed in the small summary."""
    metrics = row.get('native_resources')
    require(isinstance(metrics, dict), 'Profile lacks parsed native GNU resources')
    require(all(finite(metrics.get(key)) is not None and finite(metrics[key]) >= 0
                for key in ('wall', 'user', 'system', 'cpu', 'rss_kib')), 'Incomplete native process resources')
    require(abs(finite(metrics['cpu']) - finite(metrics['user']) - finite(metrics['system'])) < 1e-6,
            'Profile CPU differs from native user plus system CPU')
    return metrics


def comparison_helper_provenance(bundle, members, link):
    snapshots = []
    for filename in ['render_final_comparison.py', 'comparison_support.py']:
        local = Path(__file__).with_name(filename)
        digest = sha(local)
        matches = [name for name, row in members.items()
                   if Path(name).name == filename and row.get('sha256') == digest]
        if matches:
            snapshots.append(link(bundle / matches[0], filename) + f' SHA-256 `{digest}`')
        else:
            snapshots.append(f'`{filename}` SHA-256 `{digest}` (publication helper not included in this bundle)')
    return ('This comparison was rendered by small-record publication helpers: ' + '; '.join(snapshots)
            + '. The detailed reports, measured data and arithmetic remain independently readable; '
            'these helpers perform no Lean/checker execution or trace/archive parsing.')


def public_origin(bundle, members, stage, profile, required=False):
    origin = profile.get('receipt_origin')
    if origin is None:
        require(not required, 'Native canonical record lacks original-index receipt')
        return
    require(origin.get('binding_form') == 'derived-public-index', 'Ambiguous canonical origin binding')
    require(re.fullmatch(r'[0-9a-f]{64}', origin.get('original_index_sha256', '')) is not None,
            'Canonical origin lacks original raw index hash')
    name = ('profiles-' + stage + '/' + origin['index'])
    require(name in members and sha(bundle / name) == members[name]['sha256'] == origin.get('public_index_sha256'),
            'Canonical origin public index differs')
    index, position = read(bundle / name), origin.get('record_index')
    require(isinstance(index, list) and type(position) is int and 0 <= position < len(index),
            'Canonical origin index/position invalid')
    original = index[position]
    require(all(profile.get(key) == original.get(key) for key in
                ('module', 'repetition', 'source_sha256', 'config_sha256', 'exit_code', 'measurement_valid', 'trace_mode')),
            'Canonical record differs from source-bound origin projection')


def preserved_attempts(bundle, members, after):
    """Read small failure/diagnostic records only; never silently suppress them."""
    names = ['profiles-after/profile-attempts.json', 'profiles-after/profile-attempts-receipt.json']
    for name in names:
        require(name in members and sha(bundle / name) == members[name]['sha256'],
                'Preserved profile-attempt member missing or differs: ' + name)
    index = read(bundle / names[0])
    require(index.get('schema') == 'cloning-elaboration-profile-attempts-v1', 'Unexpected profile-attempt schema')
    rows = index.get('attempts')
    require(isinstance(rows, list) and rows, 'Missing preserved profile attempts')
    receipt = read(bundle / names[1])
    require(receipt.get('schema') == 'cloning-elaboration-profile-attempts-receipt-v1'
            and receipt.get('public_attempts_sha256') == sha(bundle / names[0])
            and re.fullmatch(r'[0-9a-f]{64}', receipt.get('original_attempts_sha256', '')) is not None
            and receipt.get('attempt_count') == len(rows)
            and len(receipt.get('attempts', [])) == len(rows), 'Preserved attempt receipt is incomplete or mismatched')
    source_hashes = read(bundle / 'after/source-config-hashes.json')
    identities = set()
    for row, saved in zip(rows, receipt['attempts']):
        p, role = row['profile'], row.get('evidence_role')
        require(role in {'failed-profile-attempt', 'diagnostic-native-control'}, 'Unknown preserved attempt role')
        require(isinstance(row.get('reason'), str) and row['reason'].strip(), 'Preserved attempt lacks exclusion reason')
        require(re.fullmatch(r'[0-9a-f]{64}', row.get('original_index_sha256', '')) is not None
                and type(row.get('original_record_index')) is int and row['original_record_index'] >= 0,
                'Preserved attempt lacks original index/hash/position binding')
        identity = (row['original_index_sha256'], row['original_record_index'])
        require(identity not in identities, 'Duplicate preserved attempt identity')
        identities.add(identity)
        require(all(saved.get(key) == row.get(key) for key in
                    ('evidence_role', 'reason', 'original_index', 'original_index_sha256', 'original_record_index',
                     'input_prefix', 'expected_missing_inputs'))
                and saved.get('module') == p['module'] and saved.get('exit_code') == p['exit_code']
                and saved.get('source_sha256') == p['source_sha256'], 'Preserved attempt receipt row differs')
        origin_name = 'profiles-after/' + row['original_index']
        require(origin_name in members and sha(bundle / origin_name) == members[origin_name]['sha256']
                == saved.get('public_index_sha256'), 'Preserved attempt public origin differs')
        origin = read(bundle / origin_name)
        require(isinstance(origin, list) and row['original_record_index'] < len(origin), 'Preserved attempt original position invalid')
        original = origin[row['original_record_index']]
        require(all(p.get(key) == original.get(key) for key in
                    ('module', 'source_sha256', 'config_sha256', 'exit_code', 'measurement_valid', 'trace_mode')),
                'Preserved attempt differs from its public origin projection')
        require(p.get('benchmark_commit') == after['commit'] and p.get('source_matches_benchmark') is True
                and p.get('config_matches_benchmark') is True
                and source_hashes.get('formalization/' + p['source']) == p.get('source_sha256'),
                'Preserved attempt does not bind the measured after source')
        require(finite(p.get('wall_seconds')) is not None and finite(p['wall_seconds']) >= 0,
                'Preserved attempt lacks actual wrapper duration')
        if role == 'failed-profile-attempt':
            require(p.get('exit_code') != 0 and p.get('measurement_valid') is False
                    and profile_mode(p) == 'firefox' and row.get('expected_missing_inputs') == ['events'],
                    'Failed trace attempt mislabeled as successful or fabricated Firefox export')
            require(saved.get('event_status') == 'not-produced', 'Failed attempt fabricated Firefox output')
        else:
            require(p.get('exit_code') == 0 and profile_mode(p) == 'native'
                    and row.get('expected_missing_inputs') == [], 'Exploratory native attempt mislabeled')
            require(saved.get('event_status') == 'disabled', 'Native attempt fabricated Firefox output')
    return rows


def gate(bundle, manifest):
    """Validate selected small bundle members and saved completion receipts only."""
    require(manifest.get('schema') == 'cloning-elaboration-evidence-bundle-v1', 'Unexpected bundle manifest')
    require((bundle / 'manifest.sha256').read_text().split()[0] == sha(bundle / 'manifest.json'), 'Manifest checksum differs')
    require(manifest.get('archives') and all(x.get('extraction_validated') is True for x in manifest['archives']),
            'Bundle lacks successful extraction/hash validation receipts')
    members = {row['path']: row for row in manifest['members']}
    selected = ['before/summary.json', 'after/summary.json', 'before/source-config-hashes.json',
                'after/source-config-hashes.json', 'profiles-before/summary.json', 'profiles-after/summary.json',
                'source-api-guard/cleanup-api-source-guard.json', 'source-api-guard/receipt.json']
    for name in selected:
        require(name in members and sha(bundle / name) == members[name]['sha256'], 'Selected bundle member differs: ' + name)
    before, after = read(bundle / selected[0]), read(bundle / selected[1])
    for stage, summary in [('before', before), ('after', after)]:
        validate_summary(summary)
        if stage == 'after':
            require(summary.get('source_config_hashes_unchanged') is True, 'After source/config guard failed')
        else:
            stable = summary.get('source_config_hashes_unchanged') is True
            supplemental = bundle / 'before/source-config-stability.json'
            if supplemental.is_file():
                stable |= read(supplemental).get('unchanged') is True
            require(stable, 'Before source/config guard missing')
        profile_summary = read(bundle / ('profiles-' + stage) / 'summary.json')
        require(profile_summary.get('schema') == 'cloning-elaboration-profile-summary-v1', 'Unexpected profile schema')
        rows = profile_summary['profiles']
        require(profile_summary['profile_count'] == len(rows), 'Profile count differs')
        required = {row['module'] for row in summary['timings'][:5]}
        for row in rows:
            p = row['profile']
            require(p.get('exit_code') == 0 and p.get('measurement_valid') is True
                    and p.get('source_matches_benchmark') is True and p.get('config_matches_benchmark') is True
                    and p.get('benchmark_commit') == summary['commit'], 'Incomplete or mismatched profile')
            mode = profile_mode(p)
            require(stage == 'after' or mode == 'firefox', 'Before matched cohort must contain Firefox profiles')
            if mode == 'native':
                require(p.get('module') in required, 'Native diagnostic must be an after cold-top-five module')
                require(p.get('inputs_stable') is True and p.get('build_setup_unchanged') is True
                        and p.get('build_trace_unchanged') is True and p.get('import_artifacts_unchanged') is True,
                        'Native control lacks completed setup/trace/import guards')
                require(row.get('firefox_profile') is None, 'Native control claims Firefox analysis')
        require(required <= {row['profile']['module'] for row in rows}, 'Cold top five warm profiles incomplete')
    return before, after, members


def render(bundle, before_report, after_report, output):
    manifest = read(bundle / 'manifest.json')
    before, after, members = gate(bundle, manifest)
    common = snapshot_comparison(before, after)
    root = output.parent
    def link(path, label):
        return f'[{label}]({Path(os.path.relpath(path, root)).as_posix()})'
    canonical = {stage: profile_rows(bundle, stage) for stage in ['before', 'after']}
    profiled = {stage: set(canonical[stage]) for stage in ['before', 'after']}
    require(profiled['before'] <= profiled['after'], 'Matched before warm modules are missing after')
    require(all(profile_mode(canonical['after'][name]['profile']) == 'firefox' for name in profiled['before']),
            'Native control cannot replace a matched Firefox profile')
    native_names = {name for name, row in canonical['after'].items() if profile_mode(row['profile']) == 'native'}
    require(native_names <= profiled['after'] - profiled['before'], 'Native controls must remain unmatched')
    for stage in ['before', 'after']:
        for row in canonical[stage].values():
            public_origin(bundle, members, stage, row['profile'], required=profile_mode(row['profile']) == 'native')
    attempts = preserved_attempts(bundle, members, after) if native_names else []
    guard = read(bundle / 'source-api-guard/cleanup-api-source-guard.json')
    require(guard.get('owned_sources_checked') == before['module_count']
            and guard.get('unchanged_owned_sources') + len(guard.get('proof_only_changes', [])) == before['module_count']
            and all(row.get('statement_byte_identical') is True and row.get('source_outside_body_byte_identical') is True
                    for row in guard['proof_only_changes']), 'Source/API guard scope differs')
    configs = [read(bundle / stage / 'source-config-hashes.json') for stage in ['before', 'after']]
    changed_sources = {row['source'] for row in guard['proof_only_changes']}
    require(set(configs[0]) == set(configs[1]) and {name for name in configs[0] if configs[0][name] != configs[1][name]} == changed_sources,
            'After inputs differ outside accepted proof-body source files')
    for row in guard['proof_only_changes']:
        require(configs[0][row['source']] == row['source_before_sha256'] and configs[1][row['source']] == row['source_after_sha256'],
                'Source/API guard candidate hashes differ from measured snapshots')
    matched_rows = []
    for name in canonical['before']:
        old, new = native_metrics(canonical['before'][name]), native_metrics(canonical['after'][name])
        matched_rows.append([name, number(old['wall']), number(new['wall']), number(old['cpu']), number(new['cpu'])])
    extra_rows = []
    for name in canonical['after']:
        if name not in canonical['before']:
            metrics = native_metrics(canonical['after'][name])
            extra_rows.append([name, profile_mode(canonical['after'][name]['profile']), number(metrics['wall']),
                               number(metrics['cpu']), number(metrics['rss_kib'], 0)])
    verdicts = []
    for member in sorted(members):
        if member.startswith('interventions/') and member.endswith('/verdict.json'):
            path = bundle / member
            require(sha(path) == members[member]['sha256'], 'Intervention verdict hash differs')
            verdicts.append((path.parent.name, path, intervention(read(path))))
    require(len(verdicts) == 2 and all(row[2]['decision'] == 'accept' for row in verdicts), 'Two accepted intervention verdicts required')
    metric_labels = [('GNU elapsed wall seconds', 'gnu_wall_seconds'), ('GNU user CPU seconds', 'gnu_user_cpu_seconds'),
                     ('GNU system CPU seconds', 'gnu_system_cpu_seconds'), ('GNU total CPU seconds', 'gnu_total_cpu_seconds'),
                     ('Maximum-process RSS KiB', 'max_process_rss_kib'), ('Owned modules', 'module_count'),
                     ('Native CPU / wall ratio', 'cpu_wall_ratio'),
                     ('Physical lines', 'total_lines'), ('Code lines', 'code_lines'), ('Legacy header files', 'legacy_header_files'),
                     ('Whole-log warnings', 'warnings'), ('Rounded elapsed job sum seconds', 'rounded_logged_job_seconds')]
    metric_rows = []
    for label, key in metric_labels:
        row = common['metrics'][key]
        # Percent savings are meaningful for durations/CPU, not warning/size counts.
        percent = number(row['reduction_percent']) + '%' if key in {'gnu_wall_seconds','gnu_user_cpu_seconds','gnu_system_cpu_seconds','gnu_total_cpu_seconds'} else '—'
        metric_rows.append([label, number(row['before']), number(row['after']), number(row['delta_after_minus_before']), percent])
    body = ['# Cloning elaboration cleanup comparison — 6 October 2026 campaign',
            'The dead-code sweep preceded the first test. Two measured proof conversions were then replaced, followed by the complete second test and serial warm profiles. '
            'The before/after filename date identifies the campaign that started on 6 October in Pacific time; precise UTC windows below remain the timing record.',
            '## Complete cold snapshots',
            f"Before: `{before['commit']}`; `{before['start_utc']}` → `{before['end_utc']}`.\n\n"
            f"After: `{after['commit']}`; `{after['start_utc']}` → `{after['end_utc']}`.",
            table(['Recorded metric','Before','After','After − before','Observed reduction'], metric_rows),
            'These are two complete project-only snapshots on a shared host. Their aggregate wall/CPU differences are observed trends; '
            'they do not assign the entire change to the cleanup. '
            f"Native CPU divided by GNU wall is {number(common['metrics']['cpu_wall_ratio']['before'])} before and "
            f"{number(common['metrics']['cpu_wall_ratio']['after'])} after. This utilization difference is part of the scheduling/load limitation. "
            'The separate repeated controls below establish local compiler savings.',
            '## Controlled proof-body results']
    paired = []
    phases = []
    for label, path, record in verdicts:
        bare = record['modes']['bare']['median_metrics']
        traced = record['modes']['profile']['median_exclusive_elapsed_phases_ms']['tactic execution']
        paired.append([link(path, label), number(bare['wall_seconds']['before']), number(bare['wall_seconds']['after']),
                       number(bare['wall_seconds']['reduction_percent']) + '%', number(bare['cpu']['before']),
                       number(bare['cpu']['after']), number(bare['cpu']['reduction_percent']) + '%'])
        phases.append([label, number(traced['before']/1000), number(traced['after']/1000),
                       number(traced['reduction_percent']) + '%', record['run_count']])
    body += [table(['Intervention','Bare wall A s','Bare wall B s','Wall lower','Bare CPU A s','Bare CPU B s','CPU lower'],paired),
             table(['Intervention','Traced tactic A s','Traced tactic B s','Phase lower','Repeated A/B runs'],phases),
             'Each experiment used three alternating pairs with profiling and three bare pairs, 12 successful A/B runs each. '
             'Bare runs omit trace/profile/statistics flags and provide native GNU CPU evidence. Traced controls use `pp=false` in both arms; '
             'campaign warm profiles use `pp=true`. Their exclusive phase times are elapsed measurements. The ignored body-only sorry diagnostics '
             'confirmed proof cost and were excluded from accepted sources and these 24 A/B runs. Neither bare experiment demonstrated an RSS decrease; no memory gain is claimed.',
             '## Exact changes and source/API guard',
             '- Weyl: explicitly rewrite `vectorProjector x = rankOneOperator x x` before the conversion in `integral_weighted_characteristic`.',
             '- Werner: compose `traceCLM_apply`, the channel’s trace-preservation equality, and `traceCLM_apply(...).symm` in `wernerOutput_trace_one`.',
             f"The source/API guard covers {guard['owned_sources_checked']} own files: {guard['unchanged_owned_sources']} remain byte-identical; "
             'the two changed files remain byte-identical outside those theorem bodies. Public statements, hypotheses, namespace, imports, options, attributes and variables are preserved. '
             f"All {guard['public_check_count']} result-index checks are unchanged. " + link(bundle/'source-api-guard/cleanup-api-source-guard.json','Original guard') + ' and '
             + link(bundle/'source-api-guard/receipt.json','publication receipt') + ' retain the guard’s historical working-tree context; '
             'the measured before/after manifests independently bind the accepted file bytes. This is a source/API guard, not independent proof verification.',
             '## Matched warm profiles',
             table(['Matched Firefox module','Before GNU wall s','After GNU wall s','Before native CPU s','After native CPU s'], matched_rows),
             'These single campaign warm runs use Firefox tracing with `pp=true` in both snapshots. They provide matched coverage and diagnostic context; '
             'formatting/export and contemporaneous host load can change their process CPU/wall. Only the repeated bare A/B controls above support causal compiler gains. '
             'Native CPU is GNU user plus system CPU; GNU wall differs slightly from the runner’s monotonic wrapper wall.',
             '## Scope, health and measured follow-ups',
             f"All {after['module_count']} own modules compiled in each snapshot; errors/sorry messages are {before['errors']}/{before['sorry_messages']} before and "
             f"{after['errors']}/{after['sorry_messages']} after. Both preserve dependency artifact metadata and have no upstream compilation. "
             'Warnings cover the full logs and may include replayed cached upstream messages. '
             f"The matched warm cohort contains {len(profiled['before'])} Firefox files; after adds {len(extra_rows)} unmatched cold-top-five diagnostics "
             f"({len(extra_rows)-len(native_names)} Firefox and {len(native_names)} native). "
             'Own-file diagnostics cover the cold top five plus targeted files, rather than every cold top-30 module or every proof. '
             'No broad cache, simp, arithmetic, import split or module-header migration was validated. The legacy-header census is disclosed as a compatibility adaptation of the skill, '
             'rather than forcing an unmeasured export/API migration.',
             'Remaining measured leads include mixed elaboration/metavariable costs in PCTHybridMixtureFactor, import costs in PCTGlobalPhysical and PCTUnitaryTransportChannels, '
             'and diffuse typeclass work in InfiniteTraceClass. Their precise remedies remain unresolved. Thermal, AmplifierWeylThermal, PCTClosedForm and ComparisonMonotone did not '
             'clear the full phase routing floor; the bounded arithmetic calls and static import proposals earned no cleanup credit.',
             '## Interpretation limits',
             'The matched toolchain, configurations, environment overrides and host do not establish identical contemporaneous load. Other projects were active. '
             'Profiler formatting/export can inflate whole-process CPU/wall, and cumulative phase/Firefox intervals are elapsed timers with overlapping threads/functions. '
             'Rounded Lake job durations are elapsed estimates, not per-file CPU. Peak RSS is the maximum process peak, rather than simultaneous memory summed across workers. '
             'The owned weighted import-chain and CPU/core values are scheduling references, not intrinsic observed wall-time lower bounds. '
             'The baseline source/configuration stability check is explicitly supplemental; the after runner performed its built-in end check.',
             '## Detailed reports, evidence and reproduction',
             link(before_report,'Detailed 11-section before report') + ' · ' + link(after_report,'Detailed 11-section after report') + ' · '
             + link(bundle/'README.md','Evidence and fresh reproducer commands') + ' · ' + link(bundle/'manifest.json','Evidence manifest'),
             comparison_helper_provenance(bundle, members, link),
             'Use fresh output directories with pinned dependency caches. The evidence guide gives the project-only benchmark and serial profiler commands. '
             'Its accepted-intervention archives retain the variants, commands, tool/setup/import guards, native resource logs, diagnostic labeling and exact patches. '
             'Original inherited process paths are omitted from public process census data, with their source digests retained. Rebuilding a matching local setup is required on another host; '
             'saved absolute setup paths should not be executed blindly. Historical proof/kernel certificates remain separate from elaboration measurements.']
    if extra_rows:
        # This is an unmatched after-only table; no before/after savings are assigned.
        position = body.index('## Scope, health and measured follow-ups')
        body[position:position] = [
            '## Additional after-only diagnostics',
            table(['Unmatched module','Trace mode','GNU wall s','Native CPU s','Maximum-process RSS KiB'], extra_rows),
            'These newly selected cold-top-five modules have no before warm counterpart. Their times do not enter the matched table or the 24 accepted A/B runs. '
            'A native entry runs `--profile --stats` with unchanged source/options and guarded setup/imports; it has no Firefox trace, trace-class ranking or Firefox source pointers. '
            'Its C++ profile/statistics and successful native compiler execution are useful diagnostic evidence without establishing an intervention gain.'
        ]
    if attempts:
        rows = [[row['profile']['module'], row['evidence_role'], row['profile']['exit_code'],
                 number(row['profile']['wall_seconds']), row['reason']] for row in attempts]
        position = body.index('## Scope, health and measured follow-ups')
        body[position:position] = [
            '## Preserved failed and exploratory attempts',
            table(['Module','Evidence role','Exit','Attempt wrapper wall s','Exclusion reason'], rows),
            'Failed trace wall values describe unsuccessful attempts and are excluded from passing-profile timing comparisons. '
            'The preliminary native control is exploratory because its first driver inherited setup/trace guard fields. '
            'The canonical native entries above come from freshly guarded runs and remain unmatched after-only diagnostics. '
            'No heartbeat budget or proof source changed, and none of these attempts enter the 24 accepted A/B runs.',
            link(bundle / 'profiles-after/profile-attempts.json', 'Preserved attempt records') + ' · '
            + link(bundle / 'profiles-after/profile-attempts-receipt.json', 'Original index/hash/position receipt')
        ]
        explanations = [name for name in members if name.endswith('profiler-heartbeat-exception.md')]
        if explanations:
            body.insert(position + 4, 'The elaboration failures precede Firefox export. Pinned Lean tracing code supplies a plausible '
                        'instrumentation-allocation mechanism, while the precise trigger remains unmeasured. '
                        + link(bundle / explanations[0], 'Pinned-source analysis and qualifications'))
    require(all(path.is_file() for path in [before_report,after_report]), 'Detailed before/after reports must be generated first')
    for path in [before_report,after_report]:
        require(sum(line.startswith('## ') for line in path.read_text().splitlines()) == 11, 'Detailed report lacks 11 sections')
    return '\n\n'.join(body) + '\n'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bundle',type=Path,required=True)
    p.add_argument('--before-report',type=Path,required=True)
    p.add_argument('--after-report',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--final',action='store_true',help='Explicit after-data/publication gate release; never use during measurements')
    args=p.parse_args()
    require(args.final,'Wait for root to release the completed after-data and bundle gate')
    require(not args.output.exists(),'Refusing to overwrite a comparison report')
    result=render(args.bundle.resolve(),args.before_report.resolve(),args.after_report.resolve(),args.output.resolve())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open('x') as stream:stream.write(result)
    print('Final comparison rendered from completed published small evidence records; no Lean/trace/archive work performed.')

if __name__=='__main__':main()
