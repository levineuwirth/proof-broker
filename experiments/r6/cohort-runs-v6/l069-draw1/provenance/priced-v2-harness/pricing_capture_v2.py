#!/usr/bin/env python3
"""Retain the official model/cache sources without modifying an existing bundle."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess

import pricing_gate_v2 as gate


def capture(directory):
    directory.mkdir(parents=True, exist_ok=False)
    for role, url in gate.URLS.items():
        raw_path=directory/(role+'.html')
        start=datetime.now(timezone.utc).isoformat()
        argv=['curl','-q','--fail','--location','--max-redirs','0','--silent','--show-error',
              '--proto','=https','--proto-redir','=https','--max-time','45','--output',str(raw_path),'--write-out','%{json}',url]
        response=subprocess.run(argv,capture_output=True,check=True)
        finish=datetime.now(timezone.utc).isoformat()
        meta=json.loads(response.stdout)
        transfer={k:meta[k] for k in ('http_code','content_type','url_effective','ssl_verify_result')}
        transfer.update(redirects=meta['num_redirects'],download_bytes=meta['size_download'])
        raw=raw_path.read_bytes(); derived=gate.extract(raw,role)
        extract_path=directory/(role+'.extract.json')
        extract_path.write_bytes(gate.canonical(derived)+b'\n')
        receipt={'schema_version':'r6-pricing-capture-2','requested_url':url,'transfer':transfer,
                 'started_at_utc':start,'finished_at_utc':finish,'raw_sha256':gate.sha(raw),'raw_bytes':len(raw),
                 'extract_sha256':gate.sha(extract_path.read_bytes()),'extractor_sha256':gate.sha(Path(gate.__file__).read_bytes()),
                 'client_version':meta['curl_version'],'stderr':response.stderr.decode(),
                 'scope':'local capture of a public documentation response; not signed pricing or model inference'}
        (directory/(role+'.receipt.json')).write_bytes(gate.canonical(receipt)+b'\n')
    gate.source_evidence(directory)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(); capture(args.output.resolve())
    print('Retained two official pricing sources')
