import copy
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('comparison', Path(__file__).with_name('comparison_support.py'))
m = importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


def summary(cpu=10, wall='0:20', names=('A','B'), code=100):
    return {'schema':'cloning-elaboration-test-v1','exit_code':0,'errors':0,'sorry_messages':0,
            'dependency_artifacts_unchanged':True,'upstream_compilations':[],'commit':'synthetic',
            'timings':[{'module':name,'seconds':20+i} for i,name in enumerate(names)],'module_count':len(names),
            'code_lines':code,'total_lines':code+10,'legacy_header_files':len(names),'warnings':0,
            'resources':{'User time (seconds)':str(cpu),'System time (seconds)':'2',
                         'Elapsed (wall clock) time (h:mm:ss or m:ss)':wall,
                         'Maximum resident set size (kbytes)':'1024'}}

class Tests(unittest.TestCase):
    def test_sign_and_zero_denominator(self):
        self.assertEqual(m.change(10,12)['delta_after_minus_before'],2)
        self.assertEqual(m.change(10,12)['reduction_percent'],-20)
        self.assertIsNone(m.change(0,1)['reduction_percent'])
        self.assertIsNone(m.change(None,1)['delta_after_minus_before'])

    def test_native_cpu_and_elapsed_are_separate(self):
        result=m.snapshot_comparison(summary(),summary(cpu=5,wall='0:10'))
        self.assertEqual(result['metrics']['gnu_total_cpu_seconds']['before'],12)
        self.assertEqual(result['metrics']['gnu_total_cpu_seconds']['after'],7)
        self.assertEqual(result['metrics']['gnu_wall_seconds']['after'],10)
        self.assertIn('observed trends',result['interpretation'])
        self.assertFalse(result['matching_recorded_conditions']['host'])

    def test_added_and_removed_modules_are_explicit(self):
        result=m.snapshot_comparison(summary(names=('A','B')),summary(names=('B','C')))
        self.assertEqual(result['module_cohorts'],{'common':1,'added':['C'],'removed':['A']})
        self.assertEqual(len(result['largest_logged_decreases']),1)

    def test_incomplete_or_duplicate_scope_and_nonfinite_values_rejected(self):
        for edit in ({'errors':1},{'exit_code':1},{'dependency_artifacts_unchanged':False},
                     {'module_count':3},{'timings':[{'module':'A','seconds':1},{'module':'A','seconds':2}]}):
            value=summary();value.update(edit)
            with self.subTest(edit=edit),self.assertRaises(ValueError):m.validate_summary(value)
        with self.assertRaises(ValueError):m.change(float('nan'),1)

    def test_intervention_medians_use_per_run_total_cpu(self):
        rows=[]
        for kind in ('bare','profile'):
            for arm in ('A','B'):
                for user,system in ((1,100),(5,0),(9,4)):
                    row={'kind':kind,'arm':arm,'user':user,'system':system,'cpu':user+system,
                         'wall_seconds':10,'rss_kib':100}
                    if kind=='profile':row['exclusive_phase_ms']={'tactic execution':100 if arm=='A' else 10}
                    rows.append(row)
        verdict={'decision':'accept','rows':rows}
        result=m.intervention(verdict)
        metrics=result['modes']['bare']['median_metrics']
        self.assertEqual(metrics['cpu']['before'],13)
        self.assertNotEqual(metrics['cpu']['before'],metrics['user']['before']+metrics['system']['before'])
        self.assertEqual(result['modes']['profile']['median_exclusive_elapsed_phases_ms']['tactic execution']['reduction_percent'],90)
        bad=copy.deepcopy(verdict);bad['rows'][0]['cpu']=1
        with self.assertRaises(ValueError):m.intervention(bad)
        with self.assertRaises(ValueError):m.intervention({'decision':'accept','rows':rows[:-1]})

if __name__=='__main__':unittest.main()
