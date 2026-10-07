import hashlib,io,json,re,subprocess,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
CAMPAIGN=ROOT/'.verify-work/elaboration-campaign'
EDITS={
 'formalization/Cloning/WeylIdlerUniqueness.lean':('integral_weighted_characteristic','\n/-- Left and right displacement'),
 'formalization/Cloning/WernerPhysicalPullback.lean':('wernerOutput_trace_one','\n/-- A concrete normalized density state')}
sha=lambda x:hashlib.sha256(x).hexdigest()
def stripped_body(text,name,end_marker):
 start=text.index('theorem '+name+' ')
 body=text.index(' := by',start)+len(' := ')
 end=text.index(end_marker,body)
 return text[:body]+text[end:],text[start:body]
before=json.loads((CAMPAIGN/'before/summary.json').read_text())
sizes=json.loads((CAMPAIGN/'before/size.json').read_text())
changed=[];rows=[];checks_before=[];checks_after=[]
archive_bytes=subprocess.check_output(['git','archive',before['commit'],'--',
 *[row['source'] for row in sizes]],cwd=ROOT)
with tarfile.open(fileobj=io.BytesIO(archive_bytes)) as archive:
 originals={row['source']:archive.extractfile(row['source']).read() for row in sizes}
for row in sizes:
 path=row['source']
 original=originals[path]
 current=(ROOT/path).read_bytes()
 for text,destination in [(original,checks_before),(current,checks_after)]:
  for line in text.decode().splitlines():
   if re.match(r'^\s*#check\b',line):destination.append([path,line])
 if original!=current:
  changed.append(path)
  assert path in EDITS,'Unexpected owned source change: '+path
  name,end=EDITS[path]
  a,siga=stripped_body(original.decode(),name,end)
  b,sigb=stripped_body(current.decode(),name,end)
  assert a==b and siga==sigb,'Changes outside allowed theorem body: '+path
  rows.append({'source':path,'theorem':name,'statement_byte_identical':siga==sigb,
   'source_outside_body_byte_identical':a==b,'outside_body_sha256':sha(a.encode()),
   'signature_sha256':sha(siga.encode()),'source_before_sha256':sha(original),'source_after_sha256':sha(current)})
assert set(changed)==set(EDITS),'Both accepted interventions must be present'
assert checks_before==checks_after and len(checks_before)==316
configs={}
for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
 path='formalization/'+name
 a=subprocess.check_output(['git','show',before['commit']+':'+path],cwd=ROOT)
 b=(ROOT/path).read_bytes();assert a==b
 configs[path]={'sha256':sha(b),'byte_identical_to_baseline':True}
result={'schema':'cloning-elaboration-cleanup-api-source-guard-v1','baseline_commit':before['commit'],
 'current_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'owned_sources_checked':len(sizes),'unchanged_owned_sources':len(sizes)-len(changed),
 'proof_only_changes':rows,'public_check_count':len(checks_before),
 'public_check_commands_byte_identical':True,'public_check_inventory_sha256':sha(json.dumps(checks_before).encode()),
 'configuration':configs,
 'notes':['Exact source equality outside two theorem bodies preserves declarations, statements, namespace, attributes, imports, options and variables.',
  'Accepted variants were Lean-kernel checked in six controlled runs each with fixed imports/configs; no sorry variant was applied.',
  'This is a source/API guard, not an independent full-library type-exporter comparison; the final campaign runs fresh library/public/axiom checks.']}
path=CAMPAIGN/'cleanup-api-source-guard.json';path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(path);print(json.dumps(result,indent=2))
