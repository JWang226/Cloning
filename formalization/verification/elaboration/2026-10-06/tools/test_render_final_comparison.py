import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE=Path(__file__).parent
sys.path.insert(0,str(HERE))
spec=importlib.util.spec_from_file_location('final_comparison',HERE/'render_final_comparison.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


def fixture(root):
    bundle=root/'bundle';bundle.mkdir()
    names=['Cloning.WeylIdlerUniqueness','Cloning.WernerPhysicalPullback']
    sources=['formalization/'+name.replace('.','/')+'.lean' for name in names]
    members=[]
    def put(name,data):
        path=bundle/name;path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(json.dumps(data))
        members.append({'path':name,'sha256':m.sha(path)})
    for stage,cpu in [('before',10),('after',5)]:
        summary={'schema':'cloning-elaboration-test-v1','exit_code':0,'errors':0,'sorry_messages':0,
                 'dependency_artifacts_unchanged':True,'upstream_compilations':[],'source_config_hashes_unchanged':True,
                 'commit':stage,'start_utc':'2026-10-07T00:00:00+00:00','end_utc':'2026-10-07T01:00:00+00:00',
                 'timings':[{'module':name,'seconds':20+i} for i,name in enumerate(names)],'module_count':2,
                 'code_lines':10,'total_lines':12,'legacy_header_files':2,'warnings':0,
                 'resources':{'User time (seconds)':str(cpu),'System time (seconds)':'2',
                              'Elapsed (wall clock) time (h:mm:ss or m:ss)':'0:20',
                              'Maximum resident set size (kbytes)':'1024'}}
        put(stage+'/summary.json',summary)
        put(stage+'/source-config-hashes.json',{source:('a' if stage=='before' else 'b')*64 for source in sources})
        put('profiles-'+stage+'/summary.json',{'schema':'cloning-elaboration-profile-summary-v1','profile_count':2,
                                             'profiles':[{'profile':{'module':name,'exit_code':0,'measurement_valid':True,
                                                                   'source_matches_benchmark':True,'config_matches_benchmark':True,
                                                                   'benchmark_commit':stage},
                                                          'native_resources':{'wall':20,'user':cpu,'system':2,'cpu':cpu+2,'rss_kib':1024}}
                                                         for name in names]})
    put('source-api-guard/cleanup-api-source-guard.json',{'owned_sources_checked':2,'unchanged_owned_sources':0,
          'public_check_count':316,'proof_only_changes':[{'source':source,'statement_byte_identical':True,
          'source_outside_body_byte_identical':True,'source_before_sha256':'a'*64,'source_after_sha256':'b'*64} for source in sources]})
    put('source-api-guard/receipt.json',{'scope':'synthetic receipt'})
    rows=[]
    for kind in ['bare','profile']:
        for arm in ['A','B']:
            for repeat in range(3):
                row={'kind':kind,'arm':arm,'user':10 if arm=='A' else 2,'system':2,
                     'cpu':12 if arm=='A' else 4,'wall_seconds':10 if arm=='A' else 3,'rss_kib':100}
                if kind=='profile':row['exclusive_phase_ms']={'tactic execution':100 if arm=='A' else 10}
                rows.append(row)
    for label in ['weyl-bridge-ab','werner-trace-bridge-ab']:
        put('interventions/'+label+'/verdict.json',{'decision':'accept','rows':copy.deepcopy(rows)})
    manifest={'schema':'cloning-elaboration-evidence-bundle-v1','members':members,
              'archives':[{'extraction_validated':True,'scope':'synthetic receipt only'}]}
    (bundle/'manifest.json').write_text(json.dumps(manifest))
    (bundle/'manifest.sha256').write_text(m.sha(bundle/'manifest.json')+'  manifest.json\n')
    reports=[]
    for stage in ['before','after']:
        report=root/(stage+'.md');report.write_text('\n'.join('## '+str(i) for i in range(11)));reports.append(report)
    return bundle,reports,manifest


def diagnostic_fixture(bundle, manifest):
    source='Cloning/WeylIdlerUniqueness.lean'
    rows=[]
    origin=[]
    for role in ['failed-profile-attempt','diagnostic-native-control']:
        failed=role=='failed-profile-attempt'
        p={'module':'Cloning.WeylIdlerUniqueness','source':source,'source_sha256':'b'*64,
           'benchmark_commit':'after','source_matches_benchmark':True,'config_matches_benchmark':True,
           'config_sha256':{'test':'c'*64},'wall_seconds':12.5,'exit_code':1 if failed else 0,
           'measurement_valid':not failed,'trace_mode':'firefox' if failed else 'native',
           'events':'missing.json' if failed else None,'command':['lean','--profile','--stats']}
        origin.append(p)
        rows.append({'profile':p,'original_index':'diagnostic-origin.json','original_index_sha256':'d'*64,
                     'original_record_index':len(origin)-1,'input_prefix':'','evidence_role':role,
                     'reason':'Failed attempt preserved.' if failed else 'Inherited guard fields; excluded.',
                     'expected_missing_inputs':['events'] if failed else []})
    def put(name,data):
        path=bundle/name;path.write_text(json.dumps(data))
        manifest['members'].append({'path':name,'sha256':m.sha(path)})
    put('profiles-after/diagnostic-origin.json',origin)
    put('profiles-after/profile-attempts.json',{'schema':'cloning-elaboration-profile-attempts-v1','attempts':rows})
    receipt_rows=[]
    for row in rows:
        p=row['profile']
        receipt_rows.append({**{k:v for k,v in row.items() if k!='profile'},'module':p['module'],
            'trace_mode':p['trace_mode'],'exit_code':p['exit_code'],'source_sha256':p['source_sha256'],
            'public_index_sha256':m.sha(bundle/'profiles-after/diagnostic-origin.json'),
            'event_status':'not-produced' if p['exit_code'] else 'disabled'})
    put('profiles-after/profile-attempts-receipt.json',{
        'schema':'cloning-elaboration-profile-attempts-receipt-v1','original_attempts_sha256':'e'*64,
        'public_attempts_sha256':m.sha(bundle/'profiles-after/profile-attempts.json'),
        'attempt_count':len(rows),'attempts':receipt_rows})
    return rows

class Tests(unittest.TestCase):
    def test_gate_rejects_missing_completion_and_corrupt_small_member(self):
        with tempfile.TemporaryDirectory() as tmp:
            bundle,reports,manifest=fixture(Path(tmp))
            (bundle/'after/summary.json').write_text('{}')
            with self.assertRaisesRegex(ValueError,'member differs'):m.gate(bundle,manifest)
        with tempfile.TemporaryDirectory() as tmp:
            bundle,reports,manifest=fixture(Path(tmp))
            manifest['archives'][0]['extraction_validated']=False
            with self.assertRaisesRegex(ValueError,'receipts'):m.gate(bundle,manifest)

    def test_render_uses_actual_metrics_controls_and_reports(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,reports,manifest=fixture(root)
            text=m.render(bundle,*reports,root/'comparison.md')
            self.assertIn('GNU total CPU seconds | 12.00 | 7.00',text)
            self.assertIn('Bare CPU A s',text)
            self.assertIn('24 A/B runs',text)
            self.assertIn('Pacific time',text)
            self.assertIn('not independent proof verification',text)
            self.assertIn('[Detailed 11-section before report](before.md)',text)
            self.assertNotIn('PENDING',text)

    def test_render_rejects_incomplete_detailed_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,reports,manifest=fixture(root)
            reports[1].write_text('## One section only\n')
            with self.assertRaisesRegex(ValueError,'11 sections'):m.render(bundle,*reports,root/'comparison.md')

    def test_native_control_cannot_replace_matched_firefox_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);bundle,reports,manifest=fixture(root)
            path=bundle/'profiles-after/summary.json'
            data=json.loads(path.read_text())
            data['profiles'][0]['profile'].update(trace_mode='native',events=None,inputs_stable=True,
                build_setup_unchanged=True,build_trace_unchanged=True,import_artifacts_unchanged=True,
                command=['lean','--profile','--stats'])
            data['profiles'][0]['firefox_profile']=None
            path.write_text(json.dumps(data))
            for member in manifest['members']:
                if member['path']=='profiles-after/summary.json':member['sha256']=m.sha(path)
            (bundle/'manifest.json').write_text(json.dumps(manifest))
            (bundle/'manifest.sha256').write_text(m.sha(bundle/'manifest.json')+'  manifest.json\n')
            with self.assertRaisesRegex(ValueError,'cannot replace a matched'):m.render(bundle,*reports,root/'comparison.md')

    def test_native_record_never_fabricates_firefox_evidence(self):
        with self.assertRaisesRegex(ValueError,'must not claim Firefox'):
            m.profile_mode({'trace_mode':'native','events':'invented.json'})
        with self.assertRaisesRegex(ValueError,'retains Firefox'):
            m.profile_mode({'trace_mode':'native','events':None,'command':['lean','-Dtrace.profiler=true']})

    def test_cpu_is_sum_before_comparison_and_missing_resources_fail(self):
        with self.assertRaisesRegex(ValueError,'differs from native'):
            m.native_metrics({'native_resources':{'wall':1,'user':1,'system':2,'cpu':4,'rss_kib':1}})
        with self.assertRaisesRegex(ValueError,'lacks parsed native'):
            m.native_metrics({'profile':{'module':'Cloning.Foo'}})

    def test_preserved_failures_require_honest_role_and_original_position_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            bundle,reports,manifest=fixture(Path(tmp))
            diagnostic_fixture(bundle,manifest)
            members={row['path']:row for row in manifest['members']}
            rows=m.preserved_attempts(bundle,members,json.loads((bundle/'after/summary.json').read_text()))
            self.assertEqual([row['profile']['exit_code'] for row in rows],[1,0])
            receipt_path=bundle/'profiles-after/profile-attempts-receipt.json'
            receipt=json.loads(receipt_path.read_text())
            receipt['attempts'][0]['event_status']='present'
            receipt_path.write_text(json.dumps(receipt))
            members['profiles-after/profile-attempts-receipt.json']['sha256']=m.sha(receipt_path)
            with self.assertRaisesRegex(ValueError,'fabricated Firefox'):
                m.preserved_attempts(bundle,members,json.loads((bundle/'after/summary.json').read_text()))

    def test_canonical_native_requires_unambiguous_origin_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            bundle,reports,manifest=fixture(Path(tmp))
            with self.assertRaisesRegex(ValueError,'lacks original-index receipt'):
                m.public_origin(bundle,{},'after',{'module':'Cloning.Foo'},required=True)
            with self.assertRaisesRegex(ValueError,'Ambiguous canonical origin'):
                m.public_origin(bundle,{},'after',{'receipt_origin':{'sha256':'f'*64}},required=True)

if __name__=='__main__':unittest.main()
