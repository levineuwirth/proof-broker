"""Collect native resource observations; test_review.py checks their outcomes."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
import episode
import run as r6

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--run-dir',type=Path,required=True)
args=parser.parse_args()
out=args.run_dir.resolve()
out.mkdir(parents=True,exist_ok=False)
fixture=out/'fixture'
subprocess.run(['cc','-O0',str(Path(__file__).with_suffix('.c')),'-o',str(fixture)],check=True)
results=[]
for index, (ms,budget) in enumerate([(5,.004),(10,.008),(5,.004),(10,.008),(5,.004),(10,.008)]):
    name='finite_'+str(index)
    try:
        episode.stage(out,name,fixture,[str(ms)],[],wall=5,cpu=budget,memory=192*1024**2)
        ok=True
        category=None
    except episode.StageFailure as error:
        ok=False
        category=error.category
    stats=r6.read_json(out/f'stages/{name}/{name}.process.json')
    results.append({'case':name,'limit_usec':budget*1000000,'accepted':ok,'category':category,'process':stats})
try:
    episode.stage(out,'terminal_event',fixture,['terminal'],[],wall=5,cpu=1,memory=192*1024**2,capture_events=True)
    results.append({'case':'terminal_event','accepted':True})
except episode.StageFailure as error:
    results.append({'case':'terminal_event','accepted':False,'category':error.category,'process':error.stats})
r6.write_json(out/'probe.json',results)
print(json.dumps(results,indent=2))
