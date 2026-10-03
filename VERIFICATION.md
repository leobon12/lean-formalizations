# Verification record

The release contains 6,322 byte-preserved Lean modules from three selected source snapshots:

| Source commit | Included modules | Scope |
| --- | ---: | --- |
| `14bd3363a07c0197d324bacabbff072e3f9a00c5` | 1,007 | 319 BouRabeeGwynne, 31 ReflectedWalk, 657 ReflectedGMS |
| `8c270ff3965b979e2bf27828a2f28c746eabd19b` | 2,866 | 2,846 QuantumZipper and 20 required LQGDimension support modules |
| `32156ac07851dc378a0a00e3140f15646ffe38bf` | 2,449 | 2,362 LQGMetric and 87 additional LQGDimension support modules |

`source-manifest.json` records the 19 selected entry modules, their exact transitive local import closure,
original relative paths, direct imports, source commits and SHA-256 hashes. The original release's 1,007
modules and the 2,866 Quantum Zipper release modules are unchanged. New module rows have an explicit `source_commit`; older rows inherit the manifest's
original `source_commit`. Only selected proof dependencies are included, without private development history,
worker conversations, scratch files, manuscripts or unrelated projects.

## Source checks

`python3 scripts/verify.py --scan-only` checks:

- Each included file matches its source hash, byte count, module path and import list.
- The module set is exactly the transitive local import closure of the selected roots.
- All local imports resolve and are classified consistently.
- No `sorry`, `admit`, `axiom` or `sorryAx` tokens occur outside comments and strings in proof modules.
  The scan also rejects `debug.skipKernelTC`, `implemented_by`, and unsafe definitions or theorems.
- Proof directories contain no extra files, and the public source contains no symbolic links or private
  working directories.

A source scan is not a kernel check. Compilation establishes a formal proof of the Lean statement;
the result READMEs explain its mathematical scope and differences from the source paper.

## Verification evidence

The original public snapshot `93aade873b75f3236472baa5da06aead387cece1` passed a fresh build of all
1,007 project modules and the release certificate in
[GitHub Actions run 36507686824](https://github.com/leobon12/lean-formalizations/actions/runs/36507686824).
Its verification artifact records 1,007 freshly compiled modules, no reused project modules, and the
three standard axioms listed below. That successful run and its artifact were inspected for this release.

For Quantum Zipper, the upstream clean clone at `31604bd70c37138cab1357b20862851f501e23a6` passed
its build, source scan and audit (17 theorem/witness axiom reports), followed by
`leanchecker --fresh QuantumZipper` with exit code 0. The saved build, audit and kernel-replay logs were
inspected on 2026-09-30. The published source snapshot at `8c270ff3965b979e2bf27828a2f28c746eabd19b`
has no Lean, toolchain or dependency-lockfile changes from that certified commit.

The public release's **combined certificate passed** after export. It reused compiled modules from the
successful original public CI artifact and the certified Quantum Zipper clone, after checking source
equality, and compiled the combined certificate afresh. The whole-declaration audit checked 51,169 project
declarations and 138,649 reachable declarations; its only axioms were `propext`, `Classical.choice` and
`Quot.sound`. See the [machine-readable result](results/quantum-zipper/verification.json), including the
certificate hash. This was an incremental certificate check, distinct from a fresh rebuild of all 3,873
modules. The audit caches the loaded module-name list once, avoiding repeated reconstruction during traversal.

The complete Quantum Zipper public release at `bbffc9e49d5aa93300b98e24793c1d1b8647638a` subsequently
passed its fresh rebuild and combined certificate in
[GitHub Actions run 36792894039](https://github.com/leobon12/lean-formalizations/actions/runs/36792894039).

### LQG metric release

The new entrypoint is `LQGMetric.Assembly.MainFinal`. Its exact import closure has 3,400 project
modules: 2,362 LQGMetric, 931 QuantumZipper and 107 LQGDimension. The 951 modules shared with
the previous public snapshot are byte-identical, so the export adds 2,449 files without changing
any previously released proof module. All new files are copied byte-for-byte from source commit
`32156ac07851dc378a0a00e3140f15646ffe38bf`. Lean and all dependency revisions match the existing release.

The upstream certification report records a successful build, a `leanchecker --fresh` replay of
the full closure, and a per-module replay of all 3,399 project modules at commit
`0adbf04172dbadb6c33ece7cc5867b828e2e4a7b`. It records only `propext`, `Classical.choice` and
`Quot.sound` for `theorem11_proved`, `theorem12_proved` and `main_result`. Later source commits
add `LFPP/EventMeasurable.lean` and the two explicit-measurability companions; the upstream
release reports their successful build and five-result axiom audit. These are upstream
verification reports, distinct from an independent fresh build of the exported snapshot.

The public source scan checks all 6,322 files, their hashes and exact import closure. The combined
certificate now checks the LQG metric headline types, the GFF existence witness, both measurability
companions, and every declaration in the included LQGMetric modules as well as the earlier libraries.
The [result guide](results/lqg-metric/) documents the statement conventions and the source corrections.

The **combined public certificate passed** after export. It was compiled afresh against previously
built project modules after checking byte equality with the prior public release and the current
upstream checkout. The current upstream audit log was inspected: all five LQG metric declarations
reported exactly the standard three axioms. The public certificate then checked **84,734 project
declarations and 176,114 reachable declarations**, with only `propext`, `Classical.choice` and
`Quot.sound`. The [machine-readable record](results/lqg-metric/verification.json) includes the
certificate and manifest hashes. This is an incremental certificate check; the separate public
workflow performs the fresh rebuild of all 6,322 project modules.

The publication's GitHub Actions workflow independently runs the default fresh rebuild. Consult the
[workflow history](https://github.com/leobon12/lean-formalizations/actions/workflows/verify.yml)
for the result attached to the exact public commit; earlier successful runs do not certify a later commit.

## Reproduce the checks

Lean is pinned to `v4.34.0-rc2`, and Mathlib to `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`.
`lake-manifest.json` retains the exact dependency pins used by both source workspaces.
After installing [elan](https://github.com/leanprover/elan), Git and Python 3:

```sh
git clone https://github.com/leobon12/lean-formalizations.git
cd lean-formalizations
lake exe cache get
python3 scripts/verify.py
```

The default verifier compiles all 6,322 project modules from source in dependency order with at most two
Lean processes, then compiles `Certificate.lean`. It stops on compilation failure. Logs and a
machine-readable result are written under the ignored `.lake/verification/`. This mode does not use
pre-existing project oleans. `python3 scripts/verify.py --cached` explicitly permits reuse of project
oleans while still compiling the certificate afresh; the result distinguishes these modes.

The certificate checks the exact types and axiom dependencies of the four previously released proof
declarations, all eight Quantum Zipper Section 1 results, and its three companion results. It also checks
seven supporting non-vacuity declarations, including the unconditional forward-coupling addendum setup,
and the five LQG metric declarations described above.
Their precise scope is described in the [Quantum Zipper README](results/quantum-zipper/).

Finally, the certificate traverses the dependency graph of **every declaration originating in an included
project module**, allowing only `propext`, `Classical.choice` and `Quot.sound` as axioms. This covers the
included LQGDimension support modules as well as the five formalization libraries. It does not by itself
establish source-paper correspondence.
