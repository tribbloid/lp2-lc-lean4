#!/usr/bin/env sh
# Regenerate comment-free STLC_minimal production modules, tests, and demos.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

python3 - <<'PY'
from pathlib import Path
import re


def strip_comments(source):
    output = []
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                if char == '\n':
                    output.append(char)
                i += 1
        elif in_string:
            output.append(char)
            i += 1
            if char == '\\' and i < len(source):
                output.append(source[i])
                i += 1
            elif char == '"':
                in_string = False
        elif pair == '--':
            i = source.find('\n', i)
            if i == -1:
                break
        elif pair == '/-':
            output.append(' ')
            depth = 1
            i += 2
        else:
            output.append(char)
            in_string = char == '"'
            i += 1
    if depth or in_string:
        raise ValueError('Unterminated comment or string')
    result = '\n'.join(line.rstrip() for line in ''.join(output).splitlines())
    return re.sub(r'\n{3,}', '\n\n', result).strip() + '\n'


def rename(source):
    source = re.sub(r'\bSTLC\b', 'STLC_minimal', source)
    return source


roots = [
    'Lp2lc.Active.STLC.Hash',
    'Lp2lc.Active.STLC.Serial.Infer',
    'Lp2lc.Active.STLC.Serial.__Eval_certifiedByInfer',
    'Tests.STLC.Serial.InferSpec',
    'Tests.STLC.Serial.__Eval_certifiedByInferSpec',
    'Tests.STLC.TypDemo',
]
modules = {}


def collect(module):
    if module in modules:
        return
    path = Path(module.replace('.', '/') + '.lean')
    source = strip_comments(path.read_text())
    modules[module] = source
    for dependency in re.findall(r'^import\s+([^\s]+)', source, re.MULTILINE):
        dependency = dependency.replace('«', '').replace('»', '')
        if dependency.startswith(('Lp2lc.Active.STLC.', 'Tests.STLC.')):
            collect(dependency)


for module in roots:
    collect(module)

for directory in ('Lp2lc/Active/STLC_minimal', 'Tests/STLC_minimal'):
    for path in Path(directory).rglob('*.lean'):
        path.unlink()

for module, source in modules.items():
    path = Path(rename(module).replace('.', '/') + '.lean')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(rename(source))

for prefix in ('Lp2lc.Active', 'Tests'):
    imports = sorted(module for module in modules if module.startswith(prefix + '.STLC.'))
    path = Path(prefix.replace('.', '/') + '/STLC_minimal/mod.lean')
    path.write_text(''.join(f'import {rename(module)}\n' for module in imports))
PY
