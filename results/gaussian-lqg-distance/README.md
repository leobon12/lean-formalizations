# First-order fluctuations of small-γ LQG distance

Lean formalization of **Theorem 1.1** of *First-order fluctuations of small-γ Liouville quantum gravity
distance* (30 September 2026; [AI research paper](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/gaussian-lqg-distance.pdf),
AI-generated and unrefereed), developed under Leonardo Bonanno's direction with AI assistance.

The formalization covers **the whole theorem**: (1.7), (1.8) and (1.9), the limiting law N(−q/2, 3/8),
q < 0 and the uniqueness of the median of M. It is **unconditional**: its only hypotheses are that `D γ`
is the canonical γ-LQG metric for γ ∈ (0,2) and that `h` is a normalized whole-plane GFF. This includes
the note's **Lemma 2.1**, which the note's Appendix A only reduces to an unproved uniform-in-ξ version of
estimates of Ding–Dubédat–Dunlap–Falconet. That lemma is proved here.

[Exact statement](../../GaussianLQG/Frozen/MainTheorem.lean#L30-L52) ·
[Frozen definitions](../../GaussianLQG/Frozen/) ·
[Proof](../../GaussianLQG/Assembly/MainUnconditional.lean) ·
[Proof of Lemma 2.1](../../GaussianLQG/Uniform/) ·
[Focused certificate](Check.lean) · [Verification record](verification.json)

## The theorem

Let h be a whole-plane Gaussian free field normalized by h₁(0) = 0. For each γ ∈ (0,2), let D^γ_h be
the γ-LQG metric of Gwynne–Miller, with the metrics for all γ defined from the same field. Let λ_{z,w}
be the uniform probability measure on the segment from z to w, and set

> H(s,t) = (h, λ_{is,1+it}),  M = min_{y∈[0,1]} H(y,y),  q = med M.

Then:

- M has a unique median q, and **q < 0**;
- **(1.7)** (D^γ_h(0,1) − 1)/γ → (H(0,0) − q)/2 in probability as γ ↓ 0, where H(0,0) = ∫₀¹ h(x) dx;
- the limit has law **N(−q/2, 3/8)**, so **(1.8)** (D^γ_h(0,1) − 1)/γ → N(−q/2, 3/8) in law;
- **(1.9)** m_γ = 1 − (q/2)γ + o(γ) for every choice of medians m_γ of D^γ_h(0,1).

The proof declaration is `GaussianLQG.main_theorem`. Its statement, copied from
[`GaussianLQG/Frozen/MainTheorem.lean`](../../GaussianLQG/Frozen/MainTheorem.lean#L30-L52) (inside
`namespace GaussianLQG`, with `open MeasureTheory ProbabilityTheory Filter Topology Set`), is:

```lean
theorem main_theorem :
    ∀ (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (_hh : LQGMetric.IsNormalizedWPGFF h P),
    -- `q` is the unique median of `M`, and `q < 0`
    (LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) qConst ∧
      ∀ m, LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) m → m = qConst) ∧
    qConst < 0 ∧
    -- (1.7): convergence in probability
    TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) ∧
    -- the limit has law `N(-q/2, 3/8)`
    P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) =
      gaussianReal (-qConst / 2) (3 / 8 : NNReal) ∧
    -- (1.8): convergence in law to `N(-q/2, 3/8)` (indexed by `γ ∈ (0,2)`)
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((D γ (h ω)).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal (-qConst / 2) (3 / 8 : NNReal)) ∧
    -- (1.9) for every choice of medians `m_γ` of `D^γ(0,1)`
    ∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (P.map fun ω => (D γ (h ω)).1 (0, 1)) (m γ)) →
      Tendsto (fun γ => (m γ - (1 - qConst / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) :=
```

Its proof is `by exact GaussianLQG.main_theorem_impl`. The statement holds for every family `D` of
canonical metrics and every normalized field `h` on any probability space. It was frozen and audited
independently against the paper before the proof was complete; sealing changed only the one-line proof
body. [`Check.lean`](Check.lean) restates it verbatim and checks that `main_theorem` proves it.

## The seven frozen definitions

Each project definition in the statement is frozen in its own file under
[`GaussianLQG/Frozen/`](../../GaussianLQG/Frozen/). All other names come from Mathlib or from the
[LQG metric release](../lqg-metric/).

| Paper | Lean | Definition |
| --- | --- | --- |
| λ_{z,w}, (1.5) | [`segMeasure z w`](../../GaussianLQG/Frozen/SegMeasure.lean) | The image of Lebesgue measure on [0,1] under u ↦ (1 − u)z + uw. |
| the pairing (h, μ) | [`measPairing h μ`](../../GaussianLQG/Frozen/MeasPairing.lean) | `limUnder atTop (n ↦ ∫ h (bumpTest n x) dμ(x))`: the limit of the μ-integrals of h mollified at scale 2⁻ⁿ. |
| H(s,t), (1.6) | [`segPairing h s t`](../../GaussianLQG/Frozen/SegPairing.lean) | `measPairing h (segMeasure (s·i) (1 + t·i))`. |
| the dyadic points of [0,1] | [`dyadicUnit`](../../GaussianLQG/Frozen/DyadicUnit.lean) | {k/2ⁿ : n ≥ 0, 0 ≤ k ≤ 2ⁿ}. |
| M, (1.6) | [`diagMin h`](../../GaussianLQG/Frozen/DiagMin.lean) | `⨅ y ∈ dyadicUnit, segPairing h y y`. |
| q = med M, (1.6) | [`qConst`](../../GaussianLQG/Frozen/QConst.lean) | The lower median of `diagMin` under the law of the normalized whole-plane GFF. |
| D^γ_h of Gwynne–Miller | [`IsCanonicalLQGMetric γ D`](../../GaussianLQG/Frozen/IsCanonicalLQGMetric.lean) | D is a strong γ-LQG metric (measurable, Axioms I–IV), and for every whole-plane GFF plus a bounded continuous function h on any probability space, 𝔞_ε⁻¹ D^ε_h → D_h in probability, locally uniformly on ℂ × ℂ, as ε → 0⁺. |

## Correspondence with Theorem 1.1

| Paper | Lean conjunct | Comment |
| --- | --- | --- |
| M has a unique median q | `IsMedian (P.map fun ω => diagMin (h ω)) qConst ∧ ∀ m, IsMedian (…) m → m = qConst` | The note defines q as the lower median and states that M has a strictly positive continuous density. The theorem proves that q is a median of M under the given field, and the only one. |
| q < 0 | `qConst < 0` | |
| (1.7) | `TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0) (fun ω => (segPairing (h ω) 0 0 - qConst) / 2)` | Convergence in probability as γ ↓ 0. `(D γ (h ω)).1 (0, 1)` is D^γ_h(0,1), and `segPairing h 0 0` is H(0,0) = (h, λ_{0,1}), the average of h over [0,1]. |
| the limit has law N(−q/2, 3/8) | `P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) = gaussianReal (-qConst / 2) (3 / 8)` | Mathlib's Gaussian law with mean −q/2 and variance 3/8. The variance is one quarter of Var H(0,0) = 3/2 (`energy_segMeasure_zero_one`). |
| (1.8) | `TendstoInDistribution (fun (γ : Ioo 0 2) ω => …) ((𝓝[>] 0).comap Subtype.val) id (fun _ => P) (gaussianReal (-qConst / 2) (3 / 8))` | Mathlib's convergence in distribution: each variable is almost everywhere measurable, and the laws converge weakly to N(−q/2, 3/8), along γ ↓ 0 through (0,2). |
| (1.9) | `∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 → IsMedian (P.map fun ω => (D γ (h ω)).1 (0, 1)) (m γ)) → Tendsto (fun γ => (m γ - (1 - qConst / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0)` | m_γ = 1 − (q/2)γ + o(γ) for every choice of medians. The note's lower median is one such choice. |

## Statement conventions

- **The metric.** `IsCanonicalLQGMetric` is the existence clause of Gwynne–Miller's Theorem 1.2, as
  formalized in the [LQG metric release](../lqg-metric/). The parameter is ξ = γ/d_γ. The normalization
  𝔞_ε is the **lower median of the LFPP distance between the left and right sides of the unit square,
  with unrestricted paths**, which may leave the square, for the normalized field. This is the
  normalization the note states: the median D^γ_h-distance between the left and right sides of the unit
  square is one, and (1.4) imposes no path restriction. The limit satisfies it: 1 is a median of its
  crossing distance (`IsCanonicalLQGMetric.isMedian_crossFn`). A canonical metric exists for every
  γ ∈ (0,2) (`exists_isCanonicalLQGMetric`), and any two agree almost surely
  (`IsCanonicalLQGMetric.ae_eq`), so quantifying over all such families `D` speaks about "the" metric.
  The metrics for different γ are applied to the same field, as in the note.
- **The field.** `IsNormalizedWPGFF h P` comes from the LQG metric release. h is a random distribution
  whose pairings with mean-zero test functions form a centered Gaussian process with covariance
  ∬ φ(x)(−log|x − y|)ψ(y) dx dy, and h₁(0) = 0 almost surely. Probability spaces range over Lean's
  `Type` universe.
- **Medians are two-sided.** `LQGMetric.IsMedian μ m` means μ(−∞, m] ≥ 1/2 and μ[m, ∞) ≥ 1/2. The
  constant q is the lower median of M under the law of the normalized GFF, as in the note ("a median is
  the lower 1/2-quantile"). That law is selected by choice and proved unique, so q does not depend on the
  selection.
- **M over dyadic points.** The minimum over y ∈ [0,1] is written as an infimum over the dyadic points of
  [0,1]. For a continuous version of y ↦ H(y,y) the two agree. Lean's real infimum of a set unbounded
  below is 0; this convention can matter only on a null event.
- **Pairings.** `measPairing h μ` is the limit as n → ∞ of ∫⟨h, φ_{2⁻ⁿ}(· − x)⟩ μ(dx). Here φ ≥ 0 is a
  fixed smooth radial bump supported in the closed unit ball with ∫φ = 1 (`LQGMetric.bumpTest`), and
  φ_ε = ε⁻²φ(·/ε). Where the limit does not exist, `limUnder` returns one fixed but unspecified real
  number. For the GFF and the segment measures in the theorem the limit exists outside a null set, so no
  conclusion depends on that value. It then agrees almost surely with the note's L² limit under
  mollification.
- **Limits in γ.** (1.7) and (1.9) are stated along γ ↓ 0 in ℝ. (1.8) is indexed by γ ∈ (0,2), the
  only parameters for which `D γ` is specified. Values of `D γ` outside (0,2) never matter.

## Differences from the paper

### Lemma 2.1 is proved

The note's Lemma 2.1 bounds the moments of the ½-Hölder constant A_γ(K) and of I_γ(K,δ)⁻¹ uniformly for
0 < γ ≤ γ_p. Every uniformity in γ in the note rests on it. Its proof in Appendix A asserts, by
inspection, that the constants in the crossing estimates of Ding–Dubédat–Dunlap–Falconet [DDDF20] can be
chosen uniformly for ξ in a small interval (Lemma A.1). That is plausible but is not a result in the
literature, so the note only reduces Lemma 2.1 to it. The formalization proves Lemma 2.1 for the
canonical metric (`UniformMomentInput`):

1. **DDDF20 uniformly in ξ.** Corollary 17 (lower tails,
   [`cor17_unif`](../../GaussianLQG/Uniform/LowerTail.lean#L260)), Proposition 18 (upper tails,
   [`prop18_unif`](../../GaussianLQG/Uniform/UpperTail.lean#L61)) and Theorem 20 (boundedness of the
   quantile ratios Λ_n for ξ ∈ (0, 1/8],
   [`thm20_unif_holds`](../../GaussianLQG/Uniform/Thm20/Unconditional.lean#L31)) are proved with every
   constant chosen before ξ and before the probability space. They are new copies, in
   `GaussianLQG/Uniform/`, of the fixed-ξ proofs in the LQG metric release, which is reused unchanged.
2. **A corrected constant in Step 4 of Proposition 18.** The fixed-ξ proof takes c = 1/(16ξ²) and
   C = exp(c s₀²/log 2), where s₀ ≥ (2 log 3 + 3)². So C ≥ exp(729/(16ξ² log 2)), which is unbounded as
   ξ ↓ 0. Carried through the proof of Theorem 20, it would make the bound on Λ_n diverge. The proof
   only needs c ≤ 1/(16ξ²), so c* = 1/(16ξ*²) and C* = exp(c* A(ξ*)⁴/log 2) work for every
   ξ ∈ (0, ξ*] ([`p18_step4_unif`](../../GaussianLQG/Uniform/UpperTail/Step4.lean#L191)).
3. **Condition (T) and Step 5 of Theorem 20.** The fixed-ξ proof of DDDF20's Condition (T) in the LQG
   metric release uses a Hölder exponent that tends to infinity as ξ ↓ 0. It is replaced by a direct argument with exponent 2
   for ξ ≤ 1/8 ([`conditionTU_small_all`](../../GaussianLQG/Uniform/ConditionT.lean#L251)). Step 5 of
   Theorem 20 is restated with a bound that does not depend on the data.
4. **From LFPP to the metric.** These estimates give uniform moments of the ½-Hölder constant and of
   inverse separated distances for LFPP at all dyadic scales
   ([`holder_moment_unif_holds`](../../GaussianLQG/Uniform/Holder/Done.lean#L27),
   [`inv_moment_unif_holds`](../../GaussianLQG/Uniform/InverseMoments/Unconditional.lean#L27),
   [`StarBound.exists_lfppUniformMoments`](../../GaussianLQG/Uniform/Star.lean#L127)). Fatou's lemma
   passes them to the limit ε → 0 for the canonical metric
   ([`uniformMomentInput_of_lfppUniformMoments`](../../GaussianLQG/Uniform/Limit.lean#L176)). As in the
   note, γ_p depends on the moment order p.

The last sentence of Lemma 2.1, a bound C_{K,p}δ^{−c_p} for 0 < δ ≤ 1, is not used and is not formalized.

### The dimension input is proved

The note uses d_γ = 2 + O(γ) from Ding–Gwynne [DG20, Theorem 1.2]. Here it is the theorem
[`dimensionInput_holds`](../../GaussianLQG/LQG/Dimension.lean#L34): |d_γ − 2| ≤ C₀γ for small γ. It
combines the small-ξ asymptotics of the LFPP exponent from the
[small-parameter LQG dimension](../small-gamma-dimension/) release with the LFPP exponent λ_γ of
Ding–Gwynne's Theorem 1.5 and the relation (1 − λ_γ) d_γ = 2 + γ²/2, both from the LQG metric release. The other
inputs the note cites are theorems of the LQG metric release: existence and uniqueness, Weyl scaling,
coordinate change and LFPP convergence. Rotation covariance is derived here from LFPP.

### Errata adopted from the corrected rewrite

The proof follows a corrected rewrite of the note, whose errata list has 22 items. In summary:

- **Normalization.** The note attributes to Gwynne–Miller the normalization by the median of the
  *unrestricted* left–right crossing distance. The constant of Dubédat–Falconet–Gwynne–Pfeffer–Sun uses
  crossings inside the square, and Gwynne–Miller's wording is ambiguous. The unrestricted reading is
  adopted (see above), and the median fact the proof needs is then a theorem. A variant normalized by
  internal crossings is not formalized.
- **Medians.** The literature gives only that 1 is *a* median of the crossing distance, not the lower
  median. Two-sided medians are used, and (1.9) is proved for every median.
- **Exponents and identities.** The exponent p²ξ²/2 in (2.8)–(2.9) does not follow from the cited
  argument. The weaker exponent p²ξ² suffices and is used. The Parseval-type identity (2.4), stated
  without proof, is proved for an explicit frame, and the proof of Lemma 6.1 is redone so that it uses
  only that identity and finite-dimensional shifts.
- **Arguments replaced.** The Gaussian L^p estimate (3.2) is reproved with precise hypotheses, for all
  p ≥ 1. The proof of Lemma 3.1 uses Fubini over shifts and a Lipschitz representative without the
  needed quasi-invariance step; it is redone with the Weyl axiom for all shifts simultaneously, which
  needs neither. A measurable choice of geodesics is not needed. Two-parameter Kolmogorov continuity in Proposition 5.3 is replaced by dyadic
  grids and Gaussian union bounds. The identification of the limit of normalized LFPP in Appendix A.7 is
  replaced by a bounded-rescaling argument.
- **Citations.** In Appendix A, DDDF20 (5.61)–(5.67) should be (5.61)–(5.64), and the slope
  identification is DDDF20 (5.77), not [DG20, Theorem 1.5].
- **Not needed.** The strictly positive continuous density of M is not formalized; uniqueness of the
  median suffices and is proved. Omitted thresholds in γ, uniformity requirements and unstated inputs are
  made explicit.

## Verification

The export adds **167 `GaussianLQG` modules**, copied byte-for-byte from development commit
`6eb5a29e8fb37c70823e6966d3cad60e400e874a`. The theorem's local import closure has **3,570 modules**:
167 GaussianLQG, 2,362 LQGMetric, 931 QuantumZipper and 110 LQGDimension. The other 3,403 were already
part of this release and are byte-identical. Lean `v4.34.0-rc2` and Mathlib
`a4c8ef0a69f52ec80525d5086bb3542f4660faaf` match the rest of the release.

- **Kernel replay (development workspace).** `lake env leanchecker --fresh GaussianLQG.Frozen.MainTheorem`
  re-checked every declaration in the theorem's import closure, Mathlib included, in a fresh environment.
  It **exited with code 0**, with no errors, on 19 October 2026 (12 min 5 s), on the Lean sources of commit
  `6eb5a29e8`.
- **Fresh build and focused certificate (this export).** The 167 new modules were **compiled afresh
  from the exported files**, with the public verifier's per-module settings. The 3,403 previously
  released dependencies were reused from a cache after all 3,570 source files were checked byte-for-byte.
  [`Check.lean`](Check.lean) was then compiled afresh and **passed**. It checks the verbatim statement,
  prints the seven definitions, checks the dimension input, derives Lemma 2.1 for every family of
  canonical metrics and checks the uniform DDDF20 results. It rejects `sorry` and audits **52,100
  project declarations and 136,346 reachable declarations**, allowing only `propext`,
  `Classical.choice` and `Quot.sound`. See [verification.json](verification.json).
- The [public workflow](https://github.com/leobon12/lean-formalizations/actions/workflows/verify.yml)
  rebuilds every module from source and runs the combined [certificate](../../Certificate.lean), which
  includes this theorem.

To reproduce from the public repository:

```sh
lake exe cache get
lake build GaussianLQG.Frozen.MainTheorem
lake env lean results/gaussian-lqg-distance/Check.lean
lake env leanchecker --fresh GaussianLQG.Frozen.MainTheorem
```

The sources are published byte-for-byte. Some docstrings were written before Lemma 2.1 was proved and
still call it an unproved or trust input, for example in `Core/MainDefs.lean` and
`Assembly/Provider.lean`. `main_theorem` has no such hypothesis, as its statement and axiom check show.
Docstrings also cite development documents that are not part of this snapshot, such as the corrected
rewrite ("blueprint"), rulings, audits, the uniform-constants ledger and the frozen-anchor manifest.
Kernel checking establishes the Lean proof; correspondence with the paper is the subject of the
conventions above.

## Credits

The source note builds on Gwynne–Miller [GM21], Ding–Dubédat–Dunlap–Falconet [DDDF20],
Dubédat–Falconet–Gwynne–Pfeffer–Sun [DFG+20] and Ding–Gwynne [DG20]. The formalization reuses the
[LQG metric release](../lqg-metric/), which proves Gwynne–Miller's Theorems 1.1 and 1.2 together with the
results it needs from those and other works, and modules shared with the
[Quantum Zipper](../quantum-zipper/) and [small-parameter LQG dimension](../small-gamma-dimension/)
releases. The original mathematical results are due to their authors; source-file attribution is
retained. The statement was frozen and audited following Scott Armstrong's
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) workflow.

[All released formalizations](../../README.md)
