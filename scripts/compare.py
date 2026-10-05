#!/usr/bin/env python3
"""Run the pinned official Comparator on the fixed paper interfaces."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / 'comparator'
LIBRARY = 'CombinatorialContracts'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(command, *, cwd=ROOT, env=None):
    print('+ ' + ' '.join(map(str, command)), flush=True)
    subprocess.run(list(map(str, command)), cwd=cwd, env=env, check=True)


def output(command, *, cwd=ROOT):
    return subprocess.check_output(list(map(str, command)), cwd=cwd, text=True).strip()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_inputs():
    import importlib.util
    module_spec=importlib.util.spec_from_file_location('publication',ROOT/'scripts/verify.py')
    publication=importlib.util.module_from_spec(module_spec);module_spec.loader.exec_module(publication)
    project=publication.check_inputs()
    config=json.loads((SPEC/'config.json').read_text())
    require(config['theorem_names']==project['theorems'],'Fixed theorem inventory changed')
    require(config['definition_names']==project['definition_holes']==[],'No model or implementation holes permitted here')
    require(set(config['permitted_axioms'])==AXIOMS and config['enable_nanoda'] is False,'Unexpected axiom/kernel policy')
    require(config['challenge_module']=='StatementContracts.Challenge' and config['solution_module']=='StatementContracts.Solution','Comparison module identities changed')
    solution=(ROOT/'StatementContracts/Solution.lean').read_text()
    require('import StatementContracts.Challenge' not in solution,'Specification placeholders imported by solution')
    return config


def check_checkout(path, revision):
    require(output(['git', 'rev-parse', 'HEAD'], cwd=path) == revision,
            f'Unexpected tool revision: {path.name}')
    require(not output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=path),
            f'Modified tracked tool sources: {path.name}')


def validate_dependencies():
    packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
    require(len(packages) == 9, 'Unexpected mathematical dependency inventory')
    revisions = {}
    for package in packages:
        path = ROOT / '.lake/packages' / package['name']
        require(path.is_dir(), 'Fetch pinned mathematical dependencies with lake exe cache get')
        check_checkout(path, package['rev'])
        revisions[package['name']] = package['rev']
    return revisions


def prepare_tools(pins):
    cache = Path(os.environ.get('XDG_CACHE_HOME', str(Path.home() / '.cache')))
    tools = Path(os.environ.get('COMPARATOR_HOME',
                 str(cache / 'lean-paper-comparator' / pins['comparator']['rev']))).resolve()
    require(not tools.is_relative_to((ROOT / '.lake').resolve()),
            'Comparator tools must be outside the project writable .lake directory')
    if not (tools / '.git').exists():
        require(not tools.exists(), 'Tool path exists without a Git checkout')
        tools.parent.mkdir(parents=True, exist_ok=True)
        run(['git', 'clone', '--no-checkout', pins['comparator']['url'], tools])
        run(['git', 'checkout', '--detach', pins['comparator']['rev']], cwd=tools)
    check_checkout(tools, pins['comparator']['rev'])
    require((tools / 'lean-toolchain').read_text().strip() == pins['lean'],
            'Comparator and project toolchains differ')
    manifest = json.loads((tools / 'lake-manifest.json').read_text())
    locked = {p['name']: p['rev'] for p in manifest['packages']}
    for name in ['lean4export', 'lean4checker']:
        require(locked.get(name) == pins[name]['rev'], f'Unexpected {name} dependency pin')
    run(['lake', 'build', 'comparator', 'lean4export'], cwd=tools)
    components = {'comparator': tools}
    for name in ['lean4export', 'lean4checker']:
        components[name] = tools / '.lake/packages' / name
        check_checkout(components[name], pins[name]['rev'])
    binaries = {'comparator': tools / '.lake/build/bin/comparator',
                'lean4export': components['lean4export'] / '.lake/build/bin/lean4export'}
    require(all(p.is_file() for p in binaries.values()), 'Missing official tool executable')
    return components, binaries


def checked_run(command, env, log, expected_error=None):
    print('+ ' + ' '.join(map(str, command)), flush=True)
    with log.open('w') as handle:
        process = subprocess.Popen(list(map(str, command)), cwd=ROOT, env=env,
                                   stdout=handle, stderr=subprocess.STDOUT)
        while True:
            try:
                code = process.wait(timeout=60)
                break
            except subprocess.TimeoutExpired:
                with log.open('rb') as progress:
                    progress.seek(max(0, log.stat().st_size - 4096))
                    lines = progress.read().decode(errors='replace').splitlines()
                if lines:
                    print(f'{log.stem}: {lines[-1]}', flush=True)
    text = log.read_text(errors='replace')
    unexpected = (code == 0 or expected_error not in text) if expected_error else code != 0
    if unexpected:
        print('\n'.join(text.splitlines()[-60:]), flush=True)
    if expected_error:
        require(code != 0 and expected_error in text,
                f'Negative control did not fail for the expected reason: {log}')
        print(f'PASS: negative control {log.stem}', flush=True)
    else:
        require(code == 0, f'Comparator failed with exit {code}; see {log}')
        require('Lean default kernel accepts the solution' in text and
                'Your solution is okay!' in text, 'Missing completed kernel replay')
        print('PASS: official type comparison, axiom policy and Lean kernel replay', flush=True)
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--local', action='store_true',
                        help='explicit local mode without Linux process isolation')
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--report', type=Path, default=ROOT / '.lake/comparator-results/result.json')
    args = parser.parse_args()
    require(args.jobs > 0, 'Jobs must be positive')
    pins = json.loads((SPEC / 'toolchain.json').read_text())
    require((ROOT / 'lean-toolchain').read_text().strip() == pins['lean'], 'Toolchain changed')
    config = validate_inputs()
    dependency_revisions = validate_dependencies()
    before = output([sys.executable, 'scripts/snapshot.py'])
    started = time.time()
    landrun_hash = None
    if not args.local:
        require(platform.system() == 'Linux', 'Use --local explicitly on a non-Linux host')
        require(shutil.which('landrun') and shutil.which('systemd-run'),
                'Sandbox mode requires Landrun and a functioning user systemd session')
        landrun_path = Path(shutil.which('landrun')).resolve()
        landrun_metadata = output(['go', 'version', '-m', landrun_path])
        require(pins['landrun']['rev'][:12] in landrun_metadata,
                'Landrun executable was not built at the pinned revision')
        landrun_hash = sha(landrun_path)
        run(['systemctl', '--user', 'is-active', 'default.target'])
    components, binaries = prepare_tools(pins)
    binary_hashes = {name: sha(path) for name, path in binaries.items()}
    real_lake = shutil.which('lake')
    require(real_lake is not None, 'Lake executable not found')
    logs = ROOT / '.lake/comparator-results'
    logs.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='paper-comparator-') as directory:
        adapters = Path(directory)
        adapter = ROOT / 'scripts' / ('local-landrun.sh' if args.local else 'landrun-runner.sh')
        (adapters / 'landrun').symlink_to(adapter)
        env = os.environ.copy()
        env['LEAN_NUM_THREADS'] = str(args.jobs)
        env['PATH'] = os.pathsep.join([str(adapters), str(binaries['lean4export'].parent),
                                      env.get('PATH', '')])
        if args.local:
            print('Mode: local; operating-system sandbox disabled explicitly.', flush=True)
        else:
            env['LANDRUN_EXECUTABLE'] = str(Path(shutil.which('landrun')).resolve())
        def command(filename):
            child = [real_lake, 'env', str(binaries['comparator']), str(SPEC / filename)]
            if args.local:
                return child
            return ['systemd-run', '--user', '--pipe', '--wait', '--collect',
                    '--property=RestrictAddressFamilies=~AF_UNIX',
                    '--working-directory=' + str(ROOT),
                    '--setenv=PATH=' + env['PATH'],
                    '--setenv=HOME=' + str(Path.home()),
                    '--setenv=LEAN_NUM_THREADS=' + str(args.jobs),
                    '--setenv=LANDRUN_EXECUTABLE=' + env['LANDRUN_EXECUTABLE'], '--', *child]
        checked_run(command('config.json'), env, logs / 'comparator.log')
        checked_run(command('negative-premise.json'), env, logs / 'negative-premise.log',
                    'Challenge and solution theorem statement do not match')
        checked_run(command('negative-axiom.json'), env, logs / 'negative-axiom.log',
                    'Illegal axiom detected')
    require(output([sys.executable, 'scripts/snapshot.py']) == before,
            'Verification inputs changed during Comparator execution')
    require(validate_dependencies() == dependency_revisions,
            'Mathematical dependency revisions changed during verification')
    for name, path in components.items():
        check_checkout(path, pins[name]['rev'])
    require({name: sha(path) for name, path in binaries.items()} == binary_hashes,
            'Checking executables changed during verification')
    report = {'schema_version': 1, 'status': 'PASS',
              'source_snapshot': hashlib.sha256((before + '\n').encode()).hexdigest(),
              'mathematical_dependency_revisions': dependency_revisions,
              'platform': platform.system(), 'lean': output(['lean', '--version']),
              'comparator_revision': pins['comparator']['rev'],
              'exporter_revision': pins['lean4export']['rev'],
              'replay_library_revision': pins['lean4checker']['rev'],
              'landrun_revision': None if args.local else pins['landrun']['rev'],
              'landrun_binary_sha256': landrun_hash,
              'theorem_targets': len(config['theorem_names']),
              'definition_targets': len(config['definition_names']),
              'statement_and_definition_comparison': 'PASS', 'axiom_policy': 'PASS',
              'fresh_lean_kernel_replay': 'PASS',
              'kernel_implementation': 'Lean 4.24.0 default kernel',
              'process_isolation': 'disabled; explicit local mode' if args.local else
                                   'Landrun with systemd AF_UNIX restriction',
              'negative_controls': {'added_premise': 'REJECTED', 'unexpected_axiom': 'REJECTED'},
              'checking_binary_sha256': binary_hashes,
              'log_sha256': {path.name: sha(path) for path in
                             [logs / 'comparator.log', logs / 'negative-premise.log',
                              logs / 'negative-axiom.log']},
              'elapsed_seconds': round(time.time() - started, 3)}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError, OSError, KeyError) as error:
        print('Comparator verification failed: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
