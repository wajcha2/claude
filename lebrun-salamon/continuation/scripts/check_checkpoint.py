#!/usr/bin/env python3
"""Check checkpoint bytes and produce a dependency-aware *plan*, without Lean.

Default: read the checkpoint containing this script and print JSON. Only an
explicit --output-dir writes files. Static success never certifies a proof.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import re

FROZEN_TARGET_SHA256 = '9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296'
DECL = re.compile(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe|local|scoped)\s+)*(theorem|lemma|def|abbrev|instance|example|structure|class|inductive|axiom|opaque)\s+([A-Za-z_][A-Za-z0-9_\'.]*)')
EXTERNAL_ROOTS = {'Mathlib', 'Lean', 'Std', 'Batteries', 'Aesop', 'Qq',
                  'ProofWidgets', 'LeanSearchClient', 'ImportGraph', 'Plausible', 'Init', 'Lake'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_noncode(text):
    """Blank nested comments and strings, retaining offsets and newlines."""
    out = []; i = 0; depth = 0; string = False; escaped = False
    while i < len(text):
        c = text[i]; n = text[i + 1] if i + 1 < len(text) else ''
        if depth:
            if c == '/' and n == '-': depth += 1; out.extend('  '); i += 2; continue
            if c == '-' and n == '/': depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if string:
            out.append('\n' if c == '\n' else ' ')
            if escaped: escaped = False
            elif c == '\\': escaped = True
            elif c == '"': string = False
            i += 1; continue
        if c == '"': string = True; out.append(' '); i += 1; continue
        if c == '/' and n == '-': depth = 1; out.extend('  '); i += 2; continue
        if c == '-' and n == '-':
            while i < len(text) and text[i] != '\n': out.append(' '); i += 1
            continue
        out.append(c); i += 1
    return ''.join(out)


def scoped_names(text):
    scopes = []; names = []; errors = []
    for ln, line in enumerate(text.splitlines(), 1):
        names.append('.'.join(x[1] for x in scopes if x[0] == 'namespace'))
        m = re.fullmatch(r'\s*namespace\s+([A-Za-z_][A-Za-z0-9_\'.]*)\s*', line)
        if m: scopes.append(('namespace', m.group(1))); continue
        m = re.fullmatch(r'\s*(?:noncomputable\s+)?section(?:\s+([A-Za-z_][A-Za-z0-9_\'.]*))?\s*', line)
        if m: scopes.append(('section', m.group(1) or '')); continue
        m = re.fullmatch(r'\s*end(?:\s+([A-Za-z_][A-Za-z0-9_\'.]*))?\s*', line)
        if m:
            if not scopes: errors.append(f'line {ln}: unmatched end')
            else:
                kind, name = scopes.pop()
                if m.group(1) and m.group(1) != name:
                    errors.append(f'line {ln}: end label does not match {kind} {name}')
    if scopes: errors.append(f'unclosed scopes: {scopes}')
    return names, errors


def dependency_order(graph):
    remaining = set(graph); order = []
    while remaining:
        ready = sorted(m for m in remaining if not any(d in remaining for d in graph[m]))
        if not ready: return order, sorted(remaining)
        order.extend(ready); remaining.difference_update(ready)
    return order, []


def affected_modules(graph, changed):
    affected = set(changed)
    while True:
        nxt = affected | {m for m, deps in graph.items() if any(d in affected for d in deps)}
        if nxt == affected: return affected
        affected = nxt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--output-dir', type=Path, help='explicit directory for audit JSON and rebuild plan')
    parser.add_argument('--verify-manifest', action='store_true', help='exit nonzero if static integrity checks fail')
    args = parser.parse_args(); root = args.root.resolve(); src = root / 'source'
    errors = []; files = []; admissions = []; references = []
    sources = sorted(src.rglob('*.lean'))
    if not sources: errors.append('no Lean source files')
    for p in sources:
        rel = p.relative_to(src).as_posix(); module = rel[:-5].replace('/', '.')
        raw = p.read_text(); text = strip_noncode(raw); namespaces, scope_errors = scoped_names(text)
        errors.extend(f'{rel}: {e}' for e in scope_errors)
        imports = [d for line in re.findall(r'^import\s+([^\n]+)', text, re.M) for d in line.split()]
        counts = {t:len(re.findall(r'\b' + t + r'\b', text)) for t in ('sorry','admit','axiom','opaque')}
        files.append({'file': rel, 'module': module, 'sha256': sha(p), 'bytes': p.stat().st_size,
                      'lines': len(raw.splitlines()), 'imports': imports, 'tokens': counts})
        matches = list(DECL.finditer(text)); accounted = 0
        for i, m in enumerate(matches):
            end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
            tokens = re.findall(r'\b(sorry|admit)\b', text[m.start():end])
            if not tokens: continue
            accounted += len(tokens); line = text.count('\n', 0, m.start()) + 1; name = m.group(2)
            name = name[7:] if name.startswith('_root_.') else '.'.join(x for x in (namespaces[line - 1], name) if x)
            admissions.append({'file':rel,'line':line,'kind':m.group(1),'name':name,
                               'tokens':tokens,'published_namespace':'.PublishedInputs.' in name})
        if accounted != counts['sorry'] + counts['admit']:
            errors.append(f'{rel}: admission tokens not all assigned to declarations')
        for i, line in enumerate(text.splitlines(), 1):
            for term in ('MainStatement', 'LeBrunSalamonStatement', 'WolfHomothety'):
                if term in line: references.append({'file':rel,'line':i,'term':term})

    # Exact source-manifest membership as well as file hashes are checked.
    expected = {}; manifest_errors = []
    try:
        for line in (root / 'SOURCE.sha256').read_text().splitlines():
            m = re.fullmatch(r'([0-9a-f]{64})\s+\*?(.+)', line)
            if not m: manifest_errors.append('malformed SOURCE.sha256 line'); continue
            digest, rel = m.groups()
            if rel in expected: manifest_errors.append(f'duplicate manifest path: {rel}')
            expected[rel] = digest
        actual = {'source/' + f['file']: f['sha256'] for f in files}
        for rel in sorted(set(expected) | set(actual)):
            if expected.get(rel) != actual.get(rel): manifest_errors.append(f'source manifest mismatch: {rel}')
    except OSError as exc: manifest_errors.append(f'cannot read SOURCE.sha256: {exc.strerror}')
    errors.extend(manifest_errors)
    target = root / 'target/MainStatement.lean'
    target_hash = sha(target) if target.exists() else None
    if target_hash != FROZEN_TARGET_SHA256: errors.append('frozen MainStatement.lean hash mismatch or file missing')

    graph = {f['module']: f['imports'] for f in files}
    unknown_imports = sorted({d for deps in graph.values() for d in deps
                              if d not in graph and d.split('.')[0] not in EXTERNAL_ROOTS})
    if unknown_imports: errors.append('unresolved non-library imports: ' + ', '.join(unknown_imports))
    order, cycles = dependency_order(graph)
    if cycles: errors.append('cyclic project import dependencies: ' + ', '.join(cycles))
    try:
        prior = json.loads((root / 'audit/COMPREHENSIVE_STATIC_AUDIT_V2.json').read_text())
        baseline = {f['file']:f['sha256'] for f in prior['baseline_source_files']}
        old_order = prior['summary']['archived_rebuild_modules']
    except (OSError, ValueError, KeyError):
        baseline = {}; old_order = []; errors.append('baseline source hash audit missing or malformed')
    current = {f['file']:f['sha256'] for f in files}
    changed = {f['module'] for f in files if baseline.get(f['file']) != f['sha256']}
    removed = sorted(set(baseline) - set(current))
    if removed: errors.append('baseline source files removed: ' + ', '.join(removed))
    affected = affected_modules(graph, changed)
    published = sum(r['published_namespace'] for r in admissions)
    summary = {
        'schema': 'lebrun-portable-static-checkpoint-v1',
        'static_integrity_passed': not errors, 'kernel_verified': False, 'milestone_met': False,
        'evidence_scope': 'lexical source and hash checks only; no Lean invocation or publication verification',
        'errors': errors, 'source_manifest_passed': not manifest_errors,
        'frozen_target_sha256': target_hash, 'frozen_target_matches': target_hash == FROZEN_TARGET_SHA256,
        'source_modules':len(files),'source_lines':sum(f['lines'] for f in files),
        'token_counts':{t:sum(f['tokens'][t] for f in files) for t in ('sorry','admit','axiom','opaque')},
        'admitted_declarations':len(admissions),'published_namespace_admissions':published,
        'other_admissions':len(admissions)-published,
        'final_statement_integration': {'status':'references_present_unverified' if references else 'not_present_in_source',
                                        'references':references,'proof_verified':False},
        'source_files':files,'admissions':admissions,
    }
    plan = {
        'schema':'lebrun-dependency-rebuild-plan-v1', 'plan_only':True, 'kernel_verified':False,
        'static_integrity_passed':not errors,'errors':errors,
        'baseline':'Step3b source hashes from bundled COMPREHENSIVE_STATIC_AUDIT_V2.json',
        'changed_modules':sorted(changed),'changed_count':len(changed),'removed_files':removed,
        'dependency_graph':graph,'full_topological_order':order,
        'affected_rebuild_order':[m for m in order if m in affected],'affected_count':len(affected),
        'unaffected_prerequisites':[m for m in order if m not in affected],
        'omitted_from_archived_21_module_plan':sorted(affected-set(old_order)),
        'current_source_hashes':{f['module']:f['sha256'] for f in files},
        'reuse_requirements':[
            'Successful prior compile tied to this exact source hash.',
            'Identical Lean and mathlib revisions, compile flags and dependency configuration.',
            'Identical hashes of every exact direct imported artifact, including external libraries.',
            'Reused output artifact hash matches its successful build receipt.',
            'An upstream change invalidates all affected descendants; do not restore stale overlays.',
        ],
        'acceptance_warning':'A completed plan does not establish the milestone; native transitive admission and exact-publication audits and the frozen endpoint are also required.',
    }
    if args.output_dir is not None:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for name, obj in [('CHECKPOINT_STATIC_AUDIT.json',summary),('REBUILD_PLAN.json',plan)]:
            (args.output_dir / name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({k:v for k,v in summary.items() if k not in {'source_files','admissions'}},indent=2))
    else:
        print(json.dumps({'audit':summary,'rebuild_plan':plan},indent=2,ensure_ascii=False))
    return 1 if args.verify_manifest and errors else 0


if __name__ == '__main__':
    raise SystemExit(main())
