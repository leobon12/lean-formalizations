# Mesh-only convergence and sharper rates

The accompanying Lean result covers **every named result of the paper**: Theorem 1.1, both the qualitative convergence (9) and the **sharper rate (10)**, and **Corollary 1.2**, the random-walk consequences of Bou-Rabee–Gwynne without their regularity alternatives (I)–(III).

- Theorem 1.1: [exact statement](../../MeshRates/Statement/Theorem11Rate.lean#L69) `BouRabeeGwynne.MeshRates.MeshRatesTheorem11Statement`, [proof](../../MeshRates/Theorem11RateProof.lean#L163) `BouRabeeGwynne.MeshRates.theorem11_full`.
- Corollary 1.2: [exact statement](../../MeshRates/Statement/Corollary12.lean#L97) `BouRabeeGwynne.MeshRates.MeshRatesCorollary12Statement`, [proof](../../MeshRates/Corollary12/Full.lean#L18) `BouRabeeGwynne.MeshRates.corollary12_full`.
- [AI research paper](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/mesh-only-tilings-and-rates.pdf) (16 pages, 11 October 2026; AI-generated and unrefereed).

Let d ≥ 2. Orthogonal tilings of a set D ⊆ ℝ^d are by convex polytopes with marked points in their interiors. Cells sharing a facet are joined by an edge, and the line between their marked points is perpendicular to that facet. The conductance is facet surface volume divided by the distance between marked vertices, and the mesh ε is the largest cell diameter. No geometric alternatives I, II or III are imposed. For a bounded set U, the discrete Dirichlet problem (7) is posed on the vertices with marked point in U, with boundary values at their outside neighbours.

## Theorem 1.1

- **(9) Convergence.** Let U be bounded with closure in the interior of D, let the mesh tend to zero, and let h be C² and harmonic near the closure of U. Then (7) is eventually uniquely solvable and the discrete solutions converge uniformly to h on the vertices in U. U need not be open.
- **(10) Rate.** Let K be a bounded open set containing the closure of U. There are ε₀ > 0 and C, depending only on d, U and K, with the following property. For every orthogonal tiling of every set D with closure K ⊆ interior D and mesh ε ≤ ε₀, problem (7) is uniquely solvable for all boundary data. For every h that is C² and harmonic near the closure of K, the solution h_D satisfies

  ```text
  max_{v ∈ V[U]} |h_D(v) − h(v)| ≤ C · ‖h‖_{C²(K)} · ε^{4/(d+4)}.
  ```

  Here ‖h‖_{C²(K)} is any bound for |h|, ‖Dh‖ and ‖D²h‖ on K. The planar exponent is 2/3. Since ε₀ and C are fixed before the tiling, the estimate is uniform over all tilings and over families with bounded C² norm on K.

## Corollary 1.2

For d ≥ 2, in the setting of Bou-Rabee–Gwynne's Theorems A and B, vanishing mesh alone gives the following, without alternatives (I)–(III):

- **(a)** their Assumption D, for every bounded domain whose closure lies in the interior of the tiled set;
- **(b)** the conclusion of their Proposition 4.2. On every ball with closure in the interior of the tiled set, the walk's exit law converges to Brownian harmonic measure in the Lévy–Prokhorov metric, uniformly over all vertices in the ball;
- **(c)** the conclusion of their Theorem 4.1, in the form of the [released Lean Theorem A](../bou-rabee-gwynne/). The stopped walks converge to stopped Brownian motion, uniformly over starting points in a bounded Lipschitz domain.

## Named results

All declarations are in the namespace `BouRabeeGwynne.MeshRates`.

| Paper | Lean | File |
| --- | --- | --- |
| Lemma (8): Dirichlet problem and maximum principle | `lemma8_dirichlet_maximum` | [Section1Dirichlet.lean](../../MeshRates/Section1Dirichlet.lean) |
| Path-to-boundary paragraph, p. 3 | `mr_p3_pathToBoundary`, `wellPosed_of_mesh_le` | [PathToBoundary.lean](../../MeshRates/PathToBoundary.lean), [WellPosed.lean](../../MeshRates/WellPosed.lean) |
| Lemma 2.1, (15) | `lemma21_nu_le_tileL2_add_energy` | [Section2Comparison.lean](../../MeshRates/Section2Comparison.lean) |
| Lemma 2.2, (17) | `lemma22_bvSobolev` | [Section2Comparison.lean](../../MeshRates/Section2Comparison.lean) |
| Proposition 2.3, (21) and (23) | `prop23_defectiveNash_and_support` | [Section2Nash.lean](../../MeshRates/Section2Nash.lean) |
| Proposition 3.1, (30) and (31) | `prop31_onDiagonal_and_survival` | [Section3Heat.lean](../../MeshRates/Section3Heat.lean) |
| Lemma 4.1, (46)–(48) | `lemma41_localPowerPotential` | [Section4Clock.lean](../../MeshRates/Section4Clock.lean) |
| Lemma 4.2, (50)–(52) | `lemma42_exactClock` | [Section4Clock.lean](../../MeshRates/Section4Clock.lean) |
| Proposition 4.3, (54) | `prop43_ball_crossing_le` | [Section4Crossing.lean](../../MeshRates/Section4Crossing.lean) |
| Lemma 5.1, (64) | `lemma51_energy_and_l2_error` | [Section5Energy.lean](../../MeshRates/Section5Energy.lean) |
| Lemma 6.1, (68) | `lemma61_expectedExitTime_le` | [Section6ExitBound.lean](../../MeshRates/Section6ExitBound.lean) |
| Theorem 1.1 (9) | `theorem11_qualitative` | [Theorem11Qualitative.lean](../../MeshRates/Theorem11Qualitative.lean) |
| Theorem 1.1 (10), proof (72)–(81) | `section6_oneSided_estimate`, `theorem11_rate` | [Section6OneSided.lean](../../MeshRates/Section6OneSided.lean), [Theorem11RateProof.lean](../../MeshRates/Theorem11RateProof.lean) |
| Corollary 1.2 (a), (b), (c) | `corollary12_assumptionD`, `corollary12_harmonicMeasure`, `corollary12_stoppedWalk` | [Corollary12/](../../MeshRates/Corollary12/) |

## Differences from the paper

- **Dimension in Corollary 1.2.** The paper states no dimension there, but its proof uses Theorem 1.1, which needs d ≥ 2. The Lean corollary assumes d ≥ 2, so the case d = 1 of Bou-Rabee–Gwynne's Theorem A is not covered.
- **No path-space process.** The continuous-time walk is represented by its law at each fixed time. The stopped position is Bou-Rabee–Gwynne's discrete harmonic measure, and the expected exit time is the torsion function. Optional stopping and Dynkin's formula become identities for these objects. Proposition 4.3 is stated for exit times of vertex sets, the only stopping times in this model.
- **Lemma 4.1** is proved with an extra margin of ε around the ball. Every use of it in the paper satisfies this margin.
- **Well-posedness threshold.** The paper's threshold ρ_U depends on D, while (10) needs one that depends only on U and K; the Lean threshold has that form. The paper's claim that the closed region is finite whenever U is bounded with closure in D can fail if local finiteness holds only inside D. It holds in the small-mesh regime used throughout, and no headline statement is affected.
- **(9) is not deduced from (10)** as on p. 15. It reuses the earlier kernel-checked mesh-only proof below, which gives the same statement.
- **Corollary 1.2 (c)** reuses the released proof of Bou-Rabee–Gwynne's Theorem A, with the regularity hypothesis replaced by Theorem 1.1 (9). Part (b) also proves the compactness step that their Proposition 4.2 states without proof.

## Earlier qualitative result

The earlier proof for Theorem 1.1 of the nine-page volume-notation draft remains included: [statement](../../MeshOnly/MeshOnlyStatement.lean) `BouRabeeGwynne.MeshOnlyTheorem11Statement`, [proof](../../MeshOnly/MeshOnlyConvergence.lean) `BouRabeeGwynne.meshOnly_theorem11_proved`. It proves qualitative Dirichlet convergence from vanishing mesh, uniformly over bounded C² families on a fixed common harmonic neighbourhood.

## Source and verification

The 34 `MeshRates` modules and one new `BouRabeeGwynne` module (`AffineDiscreteHarmonic`) are unchanged source from development commit `5c9b1cf3eacb5c8d42c90c55d02a4a2e8b6566ab`. The other 381 local modules in their import closure were already part of this release and are byte-identical to that source. The [source manifest](../../source-manifest.json) records the exact import closure and hashes.

The headline statements were audited against the paper and approved on 18 October 2026. The final fidelity audit has checked the statements, every named result and the structure of the proofs. Its line-by-line review of the proof of (10) is not finished.

Use the pinned toolchain and dependencies in this repository:

```sh
lake exe cache get
lake build MeshRates.Theorem11RateProof MeshRates.Corollary12.Full MeshRates.Section1Dirichlet MeshRates.PathToBoundary MeshRates.Section2Comparison MeshRates.Section4Clock MeshRates.Section4Crossing
lake env lean results/mesh-only/Check.lean
```

[`Check.lean`](Check.lean) verifies the exact types of the headline theorems and their parts, absence of `sorry`, and the axioms of both headline results, the 13 named lemma-level results and the earlier qualitative theorem. It then audits every declaration in the included `MeshRates`, `MeshOnly` and `BouRabeeGwynne` modules. The only axioms allowed are the standard foundational axioms `propext`, `Classical.choice` and `Quot.sound`. `python3 scripts/verify.py` rebuilds the whole release, as described in [VERIFICATION.md](../../VERIFICATION.md). These checks concern the encoded statements; the mathematical scope is specified above.
