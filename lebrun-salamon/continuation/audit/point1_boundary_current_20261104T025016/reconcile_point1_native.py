"""Independently reconcile native walker messages with the publication catalog.

This is a read-only evidence consumer.  It never runs Lean, changes proof source,
or certifies compiler/ancestor provenance from log text alone.  The caller must
supply the frozen source directory used by the separately validated replay.
Even complete publication coverage leaves overall Point1 acceptance to the
coherent replay, public-signature and downstream-compatibility gates.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--targets', type=Path, required=True)
    parser.add_argument('--catalog', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--log', type=Path, action='append', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if 'source' in args.output.parts:
        raise SystemExit('The evidence output must not be inside a source directory.')
    targets = read_json(args.targets)
    catalog_doc = read_json(args.catalog)
    catalog = catalog_doc['reviewed_leaf_catalog']
    expected = {row['declaration']: row for row in targets['roots']}
    if len(expected) != 44 or sum(r['scope'] == 'point1' for r in expected.values()) != 43:
        raise SystemExit('Unexpected fixed original-root denominator.')

    roots: dict[str, dict] = {}
    leaf_occurrences: dict[str, list] = defaultdict(list)
    errors: list[dict] = []
    diagnostics: list[dict] = []
    raw_logs = []
    allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound', 'sorryAx'}
    axiom_prints: dict[str, list] = defaultdict(list)
    unexpected_axiom_events: list[dict] = []

    def without_universes(name: str) -> str:
        # These annotations belong to the pretty-printer, not the constant name.
        # Strip only the explicit .{...} syntax; never abbreviate namespaces.
        return re.sub(r'\.\{[^}]*\}', '', name).strip()

    def root_record(name: str) -> dict:
        return roots.setdefault(name, {'root': name, 'direct_leaves': {},
                                      'summaries': [], 'custom_axioms': [],
                                      'missing_constants': [], 'nonstandard_axioms': []})

    for path in args.log:
        raw_logs.append({'path': str(path.resolve()), 'sha256': sha(path.read_bytes())})
        current_root = None
        for line_no, raw in enumerate(path.read_text().splitlines(), 1):
            if not raw.strip():
                continue
            try:
                item = json.loads(raw)
            except json.JSONDecodeError:
                errors.append({'kind': 'non_json_native_output', 'log': str(path), 'line': line_no})
                continue
            data = item.get('data', '')
            where = {'log': str(path.resolve()), 'line': line_no}
            if item.get('severity') == 'error':
                diagnostics.append({**where, 'data': data})
            axiom_match = re.fullmatch(r"'([^']+)' depends on axioms:\s*\[([\s\S]*)\]", data)
            empty_axiom_match = re.fullmatch(r"'([^']+)' does not depend on any axioms\.?", data)
            if axiom_match:
                printed_root = without_universes(axiom_match.group(1))
                axioms = sorted({s.strip() for s in without_universes(axiom_match.group(2)).split(',') if s.strip()})
                axiom_prints[printed_root].append({'axioms': axioms,
                    'unexpected_axioms': sorted(set(axioms) - allowed_axioms),
                    'native_message': data, **where})
            elif empty_axiom_match:
                printed_root = without_universes(empty_axiom_match.group(1))
                axiom_prints[printed_root].append({'axioms': [], 'unexpected_axioms': [],
                                                  'native_message': data, **where})
            elif 'depends on axioms' in data or 'does not depend on any axioms' in data:
                errors.append({'kind': 'unrecognized_axiom_print_format', 'data': data, **where})
            if data.startswith(('UNEXPECTED_AXIOM ', 'NONSTANDARD_AXIOM ')):
                unexpected_axiom_events.append({'root': current_root, 'data': data, **where})
                root_record(current_root or '<unbound>')['nonstandard_axioms'].append({'data': data, **where})
            if data.startswith('ROOT '):
                current_root = data.removeprefix('ROOT ').strip()
                root_record(current_root)
            elif data.startswith('DIRECT_SORRY '):
                m = re.fullmatch(r'DIRECT_SORRY (\S+)\nMODULE (\S+)\nSHORTEST_PATH (.*?)\nTYPE ([\s\S]+)', data)
                if not m:
                    errors.append({'kind': 'malformed_direct_leaf', **where})
                    continue
                name, module, route, typ = m.groups()
                route = route.split(' -> ')
                root = route[0]
                if current_root is not None and root != current_root:
                    errors.append({'kind': 'root_route_mismatch', 'root': current_root, 'route': route, **where})
                occurrence = {'name': name, 'module': module, 'shortest_path': route,
                              'native_type': typ, 'native_type_sha256': sha(typ.encode()), **where}
                existing = root_record(root)['direct_leaves'].get(name)
                if existing and (existing['native_type'] != typ or existing['module'] != module):
                    errors.append({'kind': 'inconsistent_duplicate_leaf', 'root': root, 'name': name})
                root_record(root)['direct_leaves'][name] = occurrence
                leaf_occurrences[name].append({'root': root, **occurrence})
            elif data.startswith('SUMMARY root='):
                fields = dict(re.findall(r'(\w+)=(\S+)', data))
                root = fields.pop('root')
                summary = {k: int(v) for k, v in fields.items()}
                root_record(root)['summaries'].append({**summary, **where})
            elif data.startswith('PROJECT_AXIOM '):
                root_record(current_root or '<unbound>')['custom_axioms'].append({'data': data, **where})
            elif data.startswith('MISSING_CONSTANT '):
                root_record(current_root or '<unbound>')['missing_constants'].append({'data': data, **where})

    reconciled_roots = []
    for name, target in expected.items():
        record = roots.get(name)
        root_source = args.source_root / (target['module'].replace('.', '/') + '.lean')
        observed_sha = sha(root_source.read_bytes()) if root_source.exists() else None
        result = {'id': target['id'], 'scope': target['scope'], 'root': name,
                  'module': target['module'], 'target_source_sha256': target['source_sha256'],
                  'supplied_source_sha256': observed_sha,
                  'source_matches_target': observed_sha == target['source_sha256'],
                  'present_in_native_output': record is not None,
                  'native_summary_consistent': False}
        printed = axiom_prints.get(name, [])
        axiom_sets = {tuple(p['axioms']) for p in printed}
        result.update({'native_axiom_prints': printed,
                       'native_axiom_print_present': bool(printed),
                       'native_axiom_prints_consistent': len(axiom_sets) == 1,
                       'unexpected_axioms_all_modules': sorted({a for p in printed for a in p['unexpected_axioms']}),
                       'only_allowed_axioms_in_all_module_print': bool(printed) and len(axiom_sets) == 1
                           and not any(p['unexpected_axioms'] for p in printed)})
        if record:
            summaries = record['summaries']
            expected_keys = ['all_constants', 'project_constants', 'direct_sorry_count',
                             'missing_count', 'custom_project_axiom_count']
            consistent = bool(summaries) and all(all(k in s for k in expected_keys) for s in summaries)
            if consistent:
                first = {k: summaries[0][k] for k in expected_keys}
                consistent = all({k: s[k] for k in expected_keys} == first for s in summaries)
                consistent = consistent and first['direct_sorry_count'] == len(record['direct_leaves'])
                consistent = consistent and first['missing_count'] == len(record['missing_constants'])
                consistent = consistent and first['custom_project_axiom_count'] == len(record['custom_axioms'])
                if any('nonstandard_axiom_count' in s for s in summaries):
                    consistent = consistent and all(s.get('nonstandard_axiom_count') == len(record['nonstandard_axioms']) for s in summaries)
                    first['nonstandard_axiom_count'] = summaries[0].get('nonstandard_axiom_count')
                result['native_summary'] = first
            result.update({'native_summary_consistent': consistent,
                           'direct_leaf_names': sorted(record['direct_leaves']),
                           'direct_original_project_admissions': sorted(set(record['direct_leaves']) & set(expected)),
                           'missing_constants': record['missing_constants'],
                           'custom_axioms': record['custom_axioms'],
                           'nonstandard_axioms': record['nonstandard_axioms']})
        reconciled_roots.append(result)

    records = []
    for name, occurrences in sorted(leaf_occurrences.items()):
        reviewed = catalog.get(name)
        modules = sorted({o['module'] for o in occurrences})
        types = {o['native_type_sha256']: o['native_type'] for o in occurrences}
        file = args.source_root / (modules[0].replace('.', '/') + '.lean') if len(modules) == 1 else None
        source_sha = sha(file.read_bytes()) if file and file.exists() else None
        reviewed_hashes = sorted({h for h in [
            reviewed.get('source_sha256') if reviewed else None,
            reviewed.get('currently_inspected_source_sha256') if reviewed else None] if h})
        source_match = source_sha is not None and source_sha in reviewed_hashes
        known_eligible = bool(reviewed and reviewed.get('classification') == 'eligible_published_generic')
        row = {'name': name, 'modules': modules, 'supplied_source_sha256': source_sha,
               'reviewed_source_sha256_values': reviewed_hashes,
               'source_hash_matches_publication_review': source_match,
               'catalog_classification': reviewed.get('classification') if reviewed else 'unreviewed',
               'native_type_variants': [{'sha256': h, 'type': t} for h, t in sorted(types.items())],
               'occurrences': occurrences,
               'eligible_catalog_and_source_match': known_eligible and source_match and len(modules) == 1,
               'primary_sources': reviewed.get('primary_sources', []) if reviewed else []}
        row['hash_keys'] = [sha('\0'.join([name, modules[0], source_sha or '', h]).encode())
                            for h in sorted(types)] if len(modules) == 1 else []
        records.append(row)

    complete = all(r['present_in_native_output'] and r['native_summary_consistent'] for r in reconciled_roots)
    uncovered = [r['name'] for r in records if not r['eligible_catalog_and_source_match']]
    observed = [r for r in reconciled_roots if r['present_in_native_output']]
    observed_summaries_ok = bool(observed) and all(r['native_summary_consistent'] for r in observed)
    observed_axioms_ok = bool(observed) and all(r['only_allowed_axioms_in_all_module_print'] for r in observed)
    observed_source_ok = bool(observed) and all(r['source_matches_target'] for r in observed)
    observed_no_missing_or_custom = bool(observed) and all(
        not r.get('missing_constants') and not r.get('custom_axioms')
        and not r.get('nonstandard_axioms') and not r.get('direct_original_project_admissions') for r in observed)
    out = {'schema': 'lebrun-point1-independent-native-source-reconciliation-v1',
           'recorded_utc': datetime.now(timezone.utc).isoformat(),
           'targets_sha256': sha(args.targets.read_bytes()),
           'catalog_sha256': sha(args.catalog.read_bytes()),
           'supplied_frozen_source_root': str(args.source_root.resolve()),
           'native_logs': raw_logs,
           'point1_denominator': 43, 'additional_inherited_roots': 1,
           'observed_point1_roots': sum(r['scope'] == 'point1' for r in observed),
           'observed_additional_inherited_roots': sum(r['scope'] != 'point1' for r in observed),
           'all_observed_root_summaries_consistent': observed_summaries_ok,
           'all_observed_root_axiom_prints_allowed': observed_axioms_ok,
           'all_observed_root_sources_match_targets': observed_source_ok,
           'publication_boundary_covered_for_all_observed_roots': observed_summaries_ok
               and observed_axioms_ok and observed_source_ok and observed_no_missing_or_custom
               and not uncovered and not errors and not diagnostics and not unexpected_axiom_events
               and not (set(roots) - set(expected)),
           'complete_44_root_native_summaries_observed': complete,
           'allowed_axioms': sorted(allowed_axioms),
           'complete_44_root_all_module_axiom_prints_observed': all(r['native_axiom_print_present'] for r in reconciled_roots),
           'all44_roots_only_allowed_axioms': all(r['only_allowed_axioms_in_all_module_print'] for r in reconciled_roots),
           'unexpected_axiom_walker_events': unexpected_axiom_events,
           'unexpected_roots': sorted(set(roots) - set(expected)),
           'distinct_actual_direct_leaf_count': len(records),
           'uncovered_or_ineligible_or_source_changed_leaves': uncovered,
           'parse_errors': errors, 'native_error_diagnostics': diagnostics,
           'roots': reconciled_roots, 'direct_leaf_inventory': records,
           'compiler_exit_and_transitive_artifact_provenance_independently_required': True,
           'public_signatures_and_Conic_downstream_compatibility_independently_required': True,
           'point1_accepted': False,
           'scope': 'Exact log/type/source/catalog reconciliation only; no compiler or overall milestone claim.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'output': str(args.output), 'sha256': sha(args.output.read_bytes()),
                      'complete_44': complete, 'actual_leaf_count': len(records),
                      'uncovered': uncovered, 'parse_error_count': len(errors)}, indent=2))


if __name__ == '__main__':
    main()
