# Verification record

The selected source snapshot is commit `14bd3363a07c0197d324bacabbff072e3f9a00c5`.
`source-manifest.json` lists the exact four entry modules, their complete local import closure,
original relative paths, direct imports, and SHA-256 hashes. The release contains 1,007 original
Lean modules: 319 BouRabeeGwynne, 31 ReflectedWalk, and 657 ReflectedGMS. Their source bytes are
unchanged. Dependencies needed by the selected results are included even when they establish
more general results; unrelated development files, manuscripts, private notes, logs, and Git
history are excluded.

## Checks completed for this export

`python3 scripts/verify.py --scan-only` passed:

- Every included module matches its recorded SHA-256 hash.
- The module set is exactly the transitive local import closure of the four selected roots.
- All local imports resolve inside the release.
- The source scan found no `sorry`, `admit`, `axiom`, or `sorryAx` tokens outside comments and
  strings in the exported proof modules. It also rejects `debug.skipKernelTC`,
  `implemented_by`, and unsafe definitions or theorems.
- The proof directories contain no extra files; private working directories and public
  symbolic links are absent.

A source scan is not a kernel check, and compilation does not by itself establish that a Lean
statement matches a paper. The result READMEs specify the intended scope and known differences.

## Build and certificate

Lean is pinned by `lean-toolchain`. Mathlib and its dependencies retain the original exact pins
in `lake-manifest.json`. After installing [elan](https://github.com/leanprover/elan), Git, and Python 3, run:

```sh
git clone https://github.com/leobon12/lean-formalizations.git
cd lean-formalizations
lake exe cache get
python3 scripts/verify.py
```

The verifier compiles the 1,007 project modules from source in dependency order with at most two
Lean processes, then compiles `Certificate.lean`. It stops at the first compilation failure.
Build logs and a machine-readable result are written under the ignored `.lake/verification/`.
This default mode does not use pre-existing project oleans.

`Certificate.lean` prints the exact types and axiom dependencies of all four selected results,
checks their stated interfaces, rejects `sorryAx`, and traverses the dependency graph of **every
declaration originating in any included project module**, permitting only `propext`,
`Classical.choice`, and `Quot.sound` as axioms.

For an explicitly incremental local check, `python3 scripts/verify.py --cached` permits existing
project oleans while still compiling the certificate afresh. This mode is reported distinctly
and is not a fresh project rebuild.

**Export-time status:** the source checks above have passed. A fresh full source rebuild and a
successful run of the release certificate have not yet been recorded for this public snapshot.
The GitHub Actions run, when completed successfully, provides the fresh-build result; consult
its exact commit and logs rather than treating this document as a record of an unperformed run.
