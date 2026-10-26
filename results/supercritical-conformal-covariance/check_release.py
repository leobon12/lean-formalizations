#!/usr/bin/env python3
"""Fail-closed release check of the SCC result folder in the selected public tree.

Checks: the ten frozen anchors and exactly two frozen theorems; every frozen file is selected; no proof-status
placeholder is left in the guide; every theorem anchor is SEALED (key 1) and has a key-2 `VERDICT: PASS` record in
manifest-provenance.json (both keys = PROVED); Check.lean audits every theorem export and every supporting theorem; the
modules of the supporting theorems are selected; the pinned manuscript text extraction ships with its hash; no row comes from
a rehearsal overlay; the frozen-anchor guard passes.
"""
from __future__ import annotations
import hashlib, importlib.util, json, re, sys
from pathlib import Path
sys.dont_write_bytecode = True
here = Path(__file__).resolve().parent
root = here.parents[1]
spec = importlib.util.spec_from_file_location('frozen_guard', here / 'check_frozen_anchors.py')
module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
full = json.loads((here / 'frozen-anchor-manifest.json').read_text())
prov = json.loads((here / 'manifest-provenance.json').read_text())
source = json.loads((root / 'source-manifest.json').read_text())
selected = {row['path'] for m, row in source['modules'].items() if m.startswith('SupercriticalConformalCovariance.')}
expected = {'conformal_covariance_v1', 'domainMetric_ae_eq_of_isDomainRealization_v1'}
# Supporting theorems: proved and independently audited, not frozen and not sealed (rulings A21, A22.7, A23).
SUPPORT_EXPORTS = {'SupercriticalConformalCovariance.Root.conformal_covariance_all_xi': 'SupercriticalConformalCovariance.Root.AllXi',
                   'SupercriticalConformalCovariance.GMForm.gm_axiomIV_on_base': 'SupercriticalConformalCovariance.GMForm.Base',
                   'SupercriticalConformalCovariance.GMForm.exists_countably_universal_gm_axiomIV_on_base': 'SupercriticalConformalCovariance.GMForm.Base',
                   'SupercriticalConformalCovariance.GMForm.gm_direction_of_root': 'SupercriticalConformalCovariance.GMForm.Realization',
                   'SupercriticalConformalCovariance.GMForm.gm_zeroBoundary_covariance_on_extension': 'SupercriticalConformalCovariance.GMForm.ZeroBoundaryCovariance',
                   'SupercriticalConformalCovariance.GMForm.exists_fieldwise_gm_axiomIV_on_extension': 'SupercriticalConformalCovariance.GMForm.Functional',
                   'SupercriticalConformalCovariance.GMForm.exists_countably_universal_gm_axiomIV_on_extensions': 'SupercriticalConformalCovariance.GMForm.Countable'}
MANUSCRIPT_TXT_SHA256 = '7780c858aae06ba251c02516164f0ea4edd3835c7aeb1fc3e8dcf375db55f603'
theorems = [a for a in full['anchors'] if a['kind'] == 'theorem']
if len(full['anchors']) != 10 or {a['id'] for a in theorems} != expected:
    sys.exit('Unexpected SCC frozen surface')
if {a['path'] for a in full['anchors']} - selected:
    sys.exit('Selected tree omits a frozen anchor')
missing = sorted({m for m in SUPPORT_EXPORTS.values()} - {m for m in source['modules']})
if missing:
    sys.exit('Selected tree omits supporting-theorem modules ' + repr(missing))
overlaid = sorted(m for m, row in source['modules'].items() if row.get('rehearsal_overlay')) + sorted(prov.get('rehearsal_overlay', {}))
if overlaid:
    sys.exit('Release blocked: rehearsal-overlay files are not landed sources ' + repr(overlaid[:5]))
txt = here / 'source/supercritical-conformal-covariance.txt'
if not txt.is_file() or hashlib.sha256(txt.read_bytes()).hexdigest() != MANUSCRIPT_TXT_SHA256:
    sys.exit('Release blocked: the pinned manuscript text extraction is missing or differs from its hash')
guide = (here / 'README.md').read_text()
left = [t for t in ('PROVED (seal <commit>)', '<declaration pending>', '<ref>', '**placeholder**') if t in guide]
if left:
    sys.exit(f'Release blocked: guide proof-status placeholders remain: {left}')
unsealed = [a['id'] for a in full['anchors'] if a['state'] != 'SEALED']
if unsealed:
    sys.exit('Release blocked: draft frozen anchors ' + repr(unsealed))
no_key2 = [a['id'] for a in theorems if prov.get('key2_audits', {}).get(a['id'], {}).get('verdict') != 'VERDICT: PASS']
if no_key2:
    sys.exit('Release blocked: no key-2 VERDICT: PASS record for ' + repr(no_key2))
check = (here / 'Check.lean').read_text() if (here / 'Check.lean').is_file() else ''
unaudited = [n for n in [a['export'] for a in theorems] + sorted(SUPPORT_EXPORTS)
             if not (re.search(r'(?m)^assert_no_sorry ' + re.escape(n) + r'$', check)
                     and re.search(r'(?m)^#print axioms ' + re.escape(n) + r'$', check))]
if unaudited:
    sys.exit('Release blocked: Check.lean does not audit ' + repr(unaudited))
guard = module.Guard(root, allow_non_module=True); guard.check(full)
if guard.errors:
    sys.exit('Frozen anchor release guard failed:\n' + '\n'.join(guard.errors))
print(f'FROZEN-ANCHOR RELEASE GUARD OK: 10 sealed anchors, including 2 theorem exports with key-2 PASS; Check.lean audits them '
      f'and the {len(SUPPORT_EXPORTS)} supporting theorems; manuscript text extraction OK')
