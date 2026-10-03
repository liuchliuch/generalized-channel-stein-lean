#!/usr/bin/env python3
"""Check proof sources, Comparator boundaries, and vendored source hashes."""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def lean_code(source: str) -> str:
    """Blank nested comments and strings while retaining line numbers."""
    output: list[str] = []
    index = depth = 0
    in_string = False
    while index < len(source):
        if depth:
            if source.startswith('/-', index):
                depth += 1
                output.extend('  ')
                index += 2
            elif source.startswith('-/', index):
                depth -= 1
                output.extend('  ')
                index += 2
            else:
                output.append('\n' if source[index] == '\n' else ' ')
                index += 1
        elif in_string:
            if source[index] == '\\':
                output.extend('  ')
                index += 2
            elif source[index] == '"':
                in_string = False
                output.append(' ')
                index += 1
            else:
                output.append('\n' if source[index] == '\n' else ' ')
                index += 1
        elif source.startswith('/-', index):
            depth = 1
            output.extend('  ')
            index += 2
        elif source.startswith('--', index):
            end = source.find('\n', index)
            if end < 0:
                end = len(source)
            output.extend(' ' * (end - index))
            index = end
        elif source[index] == '"':
            in_string = True
            output.append(' ')
            index += 1
        else:
            output.append(source[index])
            index += 1
    return ''.join(output)


def imports(code: str) -> list[str]:
    return re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(\S+)', code, re.M)


def check() -> None:
    errors: list[str] = []
    files = [ROOT / 'GeneralizedChannelStein.lean']
    for directory in ['GeneralizedChannelStein', 'Paper', 'scripts', 'vendor']:
        files.extend(sorted(p for p in (ROOT / directory).rglob('*.lean')
                            if not {'.lake', '.git'}.intersection(p.relative_to(ROOT).parts)))
    codes = {path: lean_code(path.read_text()) for path in files}
    challenge = ROOT / 'Paper/Challenge.lean'
    for path, code in codes.items():
        if path == challenge:
            continue
        for match in re.finditer(r'\b(?:sorry|admit|axiom)\b', code):
            line = code[:match.start()].count('\n') + 1
            errors.append(f'{path.relative_to(ROOT)}:{line}: forbidden token {match[0]}')
        if 'Paper.Challenge' in imports(code):
            errors.append(f'{path.relative_to(ROOT)} imports the Comparator challenge')

    config = json.loads((ROOT / 'comparator/config.json').read_text())
    expected = [name.removeprefix('GeneralizedChannelStein.Paper.')
                for name in config['theorem_names']]
    if len(expected) != 54 or len(set(expected)) != 54:
        errors.append('Comparator must cover exactly 54 reviewed contracts')
    if config['challenge_module'] != 'Paper.Challenge' or config['solution_module'] != 'Paper.Proofs':
        errors.append('Unexpected Comparator module boundary')
    if set(config['permitted_axioms']) != {'propext', 'Quot.sound', 'Classical.choice'}:
        errors.append('Unexpected Comparator axiom allowance')
    if imports(codes[challenge]) != ['Paper.Statements']:
        errors.append('Comparator challenge must import only the statement specification')
    declared = re.findall(r'^theorem\s+(\w+)', codes[challenge], re.M)
    holes = re.findall(r'^theorem\s+(\w+)\s*:\s*PaperStatements\.(\w+)\s*:=\s*by\s+sorry\b',
                       codes[challenge], re.M)
    if declared != expected or holes != [(name, name) for name in expected]:
        errors.append('Comparator challenge contains unexpected declarations or proof holes')
    for name in expected:
        if not re.search(r'^def\s+' + re.escape(name) + r'\s*:\s*Prop\s*:=',
                         codes[ROOT / 'Paper/Statements.lean'], re.M):
            errors.append(f'Missing explicit paper proposition: {name}')
    if re.findall(r'^theorem\s+(\w+)', codes[ROOT / 'Paper/Proofs.lean'], re.M) != expected:
        errors.append('Comparator proof declarations do not match the specification')

    for vendor, manifest in [('first-paper', 'SOURCE_SHA256'),
                             ('first-paper/vendor/lean-quantum', 'SOURCE_SHA256'),
                             ('first-paper/vendor/physlib-state', 'source-sha256.txt')]:
        vendor_root = ROOT / 'vendor' / vendor
        for line in (vendor_root / manifest).read_text().splitlines():
            if not line.strip():
                continue
            digest, relative = line.split(maxsplit=1)
            path = vendor_root / relative.lstrip('*')
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                errors.append(f'Vendor hash mismatch: {path.relative_to(ROOT)}')
    reachable = set(module_order())
    for path in (ROOT / 'GeneralizedChannelStein').rglob('*.lean'):
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        if module not in reachable:
            errors.append(f'Unreachable project module: {module}')
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        raise SystemExit(1)
    print(f'Checked {len(files) - 1} proof-source files; no placeholders or custom axioms.')
    print('Comparator specification has 54 reviewed contracts; proof holes are isolated.')
    print('Vendored source hashes match.')


def module_order() -> list[str]:
    """Local import closure in dependency order, for small-memory builds."""
    modules: dict[str, Path] = {}
    for source_root in [ROOT, ROOT / 'vendor/first-paper',
                        ROOT / 'vendor/first-paper/vendor/lean-quantum',
                        ROOT / 'vendor/first-paper/vendor/physlib-state']:
        for path in source_root.rglob('*.lean'):
            relative = path.relative_to(source_root)
            if any(part in {'.lake', '.git', 'scripts', 'vendor', 'comparator'}
                   for part in relative.parts):
                continue
            modules['.'.join(relative.with_suffix('').parts)] = path
    seen: set[str] = set()
    ordered: list[str] = []

    def visit(name: str) -> None:
        if name in seen or name not in modules:
            return
        seen.add(name)
        for dependency in imports(lean_code(modules[name].read_text())):
            visit(dependency)
        ordered.append(name)

    visit('GeneralizedChannelStein')
    visit('Paper.Proofs')
    return ordered


if __name__ == '__main__':
    if sys.argv[1:] == ['--module-order']:
        print('\n'.join(module_order()))
    elif not sys.argv[1:]:
        check()
    else:
        raise SystemExit('Usage: python3 scripts/check_sources.py [--module-order]')
