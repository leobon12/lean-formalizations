/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CondCode
import InteractingSLE.Spec.Restart.FCDetAnnounce
import InteractingSLE.Spec.Supplement.BW1ChainCond
import InteractingSLE.Spec.Restart.DomainMarkovMeanLoc
import InteractingSLE.Spec.Supplement.CondDriverBridge

/-!
# A conditional flow line from K2's inputs (S) and (L) alone

Packet PROVE-T14-SB2COND. Every conditional identification of the supplement's Section 28 (Lemma SB2(1)–(2),
pp. 630–633; Lemma S4, p. 579; Lemma BW3a, p. 624) ends with the same step: "Conditional-mean martingale limits and
Aux. 9 therefore include the collision and terminal times with their full kernels [...] Integrated uniqueness and the
field-determining graphs identify the actual relative ordinary flows" (p. 632–633). In Lean this is the passage from
K2's inputs — the Gaussian kernels with the identified mean (S) (`HasSafeLaw`) and the history-marked locality (L)
(`HasSafeMembers`) of the relative continuation read in a retained chart — to the carrier `SB.IsCondFlowLineDriverOn`.

The landed bridge `CondDriverBridge.isCondFlowLineDriverOn_of_k2` (PROVE-T14-SB8) also asks for the **law** of the
relative driver (K2's input (E), `IsRandomWordEvolution`), which is the first missing item of
`planning/handoffs/PROVE-T14-SBFIN.md` §4 (c). This file removes it, for a continuation whose lifetime is its
continuation threshold, on a probability space of any universe:

1. K2 on the enlargement `Ω × (ℕ → ℝ)` (`Restart.FCDet.exists_ae_isOptionalHullCoupling`: the converse of
   Theorem 2.4 produces (E) there from (S));
2. Theorem 1.2 (parametric form, universe `u`) under each regular conditional law on the enlargement: the driver
   matches the canonical driver code of (word, chart field) (`ae_driverCodeMatch_of_isFlowLineDriver_univ`);
3. the code match is a Borel event of `Ω`, so it integrates back to `P` (`Sec5.Lemma56Stages.ae_of_ae_condExpKernel`,
   `Restart.ConverseBefore.ae_of_ae_fst`);
4. under `condExpKernel P 𝒢 ω₀` the word and the chart are frozen and the chart field is the GFF of the word, so the
   realization half of the code (`isFlowLineDriver_of_driverCodeMatch_univ`) gives the flow line.

* **`isCondFlowLineDriverOn_of_hasSafeLaw`**.

**R48.** Theorems 1.2–1.3 are hypotheses; the result serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cond

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.PocketTraversal Exist.Staged Sec2.Assembly

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The code-match event of `Ω` is measurable. -/
theorem measurableSet_driverCodeMatch_self {G : Ω → PCode × ℝ≥0∞} (hG : Measurable G) {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ t, Measurable (W t)) {L : Ω → ℝ≥0∞} (hL : Measurable L) :
    MeasurableSet {ω | IsDriverCodeMatch (G ω) (fun t => W t ω) (L ω)} := by
  have h := measurableSet_driverCodeMatch (C := Ω) (S := Ω) (G := fun p => G p.2) (hG.comp measurable_snd) hW hL
  have e : {ω | IsDriverCodeMatch (G ω) (fun t => W t ω) (L ω)} =
      (fun ω => (ω, ω)) ⁻¹' {p : Ω × Ω | IsDriverCodeMatch (G p.2) (fun t => W t p.2) (L p.2)} := rfl
  rw [e]
  exact (measurable_id.prodMk measurable_id) h

/-- **A conditional flow line from K2's inputs (S) and (L) alone** (no input (E)). Let the field be read through a
random conformal chart `c` (measurable in the coordinates, continuous lift, kernel-almost surely constant given `𝒢`),
and let `cw` be a `𝒢`-measurable boundary word whose angle-`θ` flow-line word has `nL`, `nR` marks with positions
`(xL, xR)` and weights `(ρL, ρR)` almost surely. Suppose: the chart field is conditionally on `𝒢` the GFF of the word
(`IsCondChartField`); the relative driver `W` is globally continuous from `0` and `𝓗`-adapted (`𝒢 ≤ 𝓗 0`); the seed
is admissible; the threshold of the geometric force points has an announcing sequence; and K2's (S) and (L) hold for
the flow-rule field `chartTransport c 1 (θχ) χ h` up to that threshold. Then `W`, with the threshold as lifetime, is
conditionally on `𝒢` the angle-`θ` flow line of the field read in `c` with the data of `cw`. (The form with the
announcing sequence `T` given; `isCondFlowLineDriverOn_of_hasSafeLaw` constructs it.) -/
theorem isCondFlowLineDriverOn_of_hasSafeLaw_ann (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {cw : Ω → BoundaryWord} (hcw : Measurable[𝒢] cw)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω))
    (hword : ∀ᵐ ω ∂P, flowLineNL (cw ω).fn (cw ω).jumps 0 = nL ∧ flowLineNR (cw ω).fn (cw ω).jumps 0 = nR ∧
      truncWord nL nR (padFL κ θ (cw ω).fn (cw ω).jumps) = ((xL ω, xR ω), (ρL, ρR)))
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) φ) P)
    (hseed : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    {T : ℕ → Ω → ℝ≥0}
    (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P (FCDet.thr ρL ρR W xL xR) T)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ (FCDet.thr ρL ρR W xL xR) W (geomLW W xL) (geomRW W xR)
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hmem : HasSafeMembers P 𝓗 univ (FCDet.thr ρL ρR W xL xR) W
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hG : IsCondChartField 𝒢 1 0 (chiC κ) P h c (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps))
    (hcc : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P univ h c (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps) W
      (FCDet.thr ρL ρR W xL xR) := by
  classical
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  set ζ : Ω → ℝ≥0∞ := FCDet.thr ρL ρR W xL xR with hζdef
  set X : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω)
    with hXdef
  set Hc : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω) with hHcdef
  have hX : Measurable X := Chart.measurable_chartTransport_random' hc hdom hfwd hliftm hlc hhm 1 _ _
  have hHc : Measurable Hc := Chart.measurable_chartTransport_random' hc hdom hfwd hliftm hlc hhm 1 0 _
  have hWm : ∀ t, Measurable (W t) := fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl
  have hζm : Measurable ζ := FCDet.measurable_thr hWc hWa (hxL.mono h𝒢 le_rfl) (hxR.mono h𝒢 le_rfl)
  have hcwm : Measurable cw := hcw.mono h𝒢m le_rfl
  -- the code-match event
  set G : Ω → PCode × ℝ≥0∞ := fun ω => driverCode h12p hκ θ (cw ω, Hc ω) with hGdef
  have hGm : Measurable G := (measurable_driverCode h12p hκ θ).comp (hcwm.prodMk hHc)
  have hQm := measurableSet_driverCodeMatch_self hGm hWm hζm
  -- (1) K2 on the enlargement
  obtain ⟨P₀, hP₀, hK⟩ := FCDet.exists_ae_isOptionalHullCoupling hκ h𝒢 hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWa
    hX hint (hseed.mono fun ω h => FCDet.thr_pos hW0 hWc hxL0 hxR0 h) hT hlaw hmem
  -- (2) the code match under almost every conditional law on the enlargement
  have hm' : 𝒢.comap Prod.fst ≤ (inferInstance : MeasurableSpace (Ω × (ℕ → ℝ))) :=
    (MeasurableSpace.comap_mono h𝒢m).trans measurable_fst.comap_le
  have hcw' : Measurable[𝒢.comap Prod.fst] fun p : Ω × (ℕ → ℝ) => cw p.1 :=
    hcw.comp (Measurable.of_comap_le le_rfl)
  have hfix := Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P.prod P₀) hm' hcw'
  have hword' := ConverseBefore.ae_fst_of_ae (P₀ := P₀) hword
  have hkm : ∀ᵐ p₀ ∂(P.prod P₀), ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀),
      p ∈ Prod.fst ⁻¹' {ω | IsDriverCodeMatch (G ω) (fun t => W t ω) (ζ ω)} := by
    filter_upwards [hK, hfix, hword'] with p₀ hp₀ hfix₀ hw₀
    obtain ⟨𝓕', W', VL', VR', B', hC, hag⟩ := hp₀
    obtain ⟨hn1, hn2, htw⟩ := hw₀
    obtain ⟨VL'', VR'', hC'⟩ := CondDriverBridge.coupling_flowLineWord_of_truncWord hn1 hn2 htw hC
    have hfl : IsFlowLineDriver κ (cw p₀.1).fn (cw p₀.1).jumps θ
        (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀) (fun p => Hc p.1) W' (fun p => ζ p.1) :=
      ⟨fun p => X p.1, 𝓕', VL'', VR'', B',
        fun p => CondDriverBridge.isTranslateAddConst_chartTransport (hc p.1) _ _ _, hC'⟩
    have hfl' := StagedReg.isFlowLineDriver_congr_ae hfl (W' := fun t (p : Ω × (ℕ → ℝ)) => W t p.1)
      (fun t => (hWm t).comp measurable_fst)
      (hag.mono fun p hp => ⟨(hp 0).1.symm, fun t _ => (hp t).1.symm⟩)
    have hdet := ae_driverCodeMatch_of_isFlowLineDriver_univ h12p hκ θ h13 (cw p₀.1) hfl'
    filter_upwards [hdet, hfix₀] with p hp hcwp
    show IsDriverCodeMatch (driverCode h12p hκ θ (cw p.1, Hc p.1)) (fun t => W t p.1) (ζ p.1)
    rw [hcwp]
    exact hp
  -- (3) back to `P`
  have hQ : ∀ᵐ ω ∂P, IsDriverCodeMatch (G ω) (fun t => W t ω) (ζ ω) :=
    ConverseBefore.ae_of_ae_fst (P₀ := P₀) (q := fun ω => IsDriverCodeMatch (G ω) (fun t => W t ω) (ζ ω))
      (Sec5.Lemma56Stages.ae_of_ae_condExpKernel hm' (measurable_fst hQm) hkm)
  -- (4) realization under the conditional laws given `𝒢`
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢m hQ,
    Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢m hcw, hcc, hG] with ω₀ hQ₀ hcw₀ hcc₀ hG₀ _
  obtain ⟨hpc, h', hct, hgff⟩ := hG₀
  set H₀ : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω) with hH₀
  have hct₀ : ∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (H₀ ω) := fun ω =>
    CondDriverBridge.isChartTransport_chartTransport_of_continuousOn (hc ω₀) (hlc ω₀) 1 0 (chiC κ) (h ω)
  have he : h' = H₀ := funext fun ω => IsChartTransport.unique (hc ω₀) (hct ω) (hct₀ ω)
  rw [he] at hgff
  refine ⟨hpc, H₀, hct₀, ?_⟩
  refine isFlowLineDriver_of_driverCodeMatch_univ h12p hκ θ h13 (cw ω₀) hgff hWm hζm
    (fun ω => (hWc ω).continuousOn) ?_
  filter_upwards [hQ₀, hcw₀, hcc₀] with ω hω hcwω hcω
  have hH : Hc ω = H₀ ω := CondDriverBridge.chartTransport_congr_chart (hc ω) (hc ω₀) hcω 1 0 (chiC κ) (h ω)
  have e : G ω = driverCode h12p hκ θ (cw ω₀, H₀ ω) := by
    simp only [hGdef]
    rw [hcwω, hH]
  rw [← e]
  exact hω

/-- **A conditional flow line from K2's inputs (S) and (L) alone**, with the announcing sequence of the threshold
constructed (`Restart.FCDet.exists_isAnnouncingSeq_thr` in the usual augmentation of `𝓗`); see
`isCondFlowLineDriverOn_of_hasSafeLaw_ann`. -/
theorem isCondFlowLineDriverOn_of_hasSafeLaw (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {cw : Ω → BoundaryWord} (hcw : Measurable[𝒢] cw)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω))
    (hword : ∀ᵐ ω ∂P, flowLineNL (cw ω).fn (cw ω).jumps 0 = nL ∧ flowLineNR (cw ω).fn (cw ω).jumps 0 = nR ∧
      truncWord nL nR (padFL κ θ (cw ω).fn (cw ω).jumps) = ((xL ω, xR ω), (ρL, ρR)))
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) φ) P)
    (hseed : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ (FCDet.thr ρL ρR W xL xR) W (geomLW W xL) (geomRW W xR)
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hmem : HasSafeMembers P 𝓗 univ (FCDet.thr ρL ρR W xL xR) W
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hG : IsCondChartField 𝒢 1 0 (chiC κ) P h c (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps))
    (hcc : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P univ h c (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps) W
      (FCDet.thr ρL ρR W xL xR) := by
  have h0U : 𝒢 ≤ usualAugmentation 𝓗 P 0 := h𝒢.trans (Ito.le_usualAugmentation 𝓗 P 0)
  have hWaU : StronglyAdapted (usualAugmentation 𝓗 P) W := fun t =>
    (hWa t).mono (Ito.le_usualAugmentation 𝓗 P t)
  obtain ⟨T, hT, -⟩ := FCDet.exists_isAnnouncingSeq_thr (ρL := ρL) (ρR := ρR) (𝓖 := usualAugmentation 𝓗 P)
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0) hWc hWaU (hxL.mono h0U le_rfl)
    (hxR.mono h0U le_rfl) hxLa hxRm (hseed.mono fun ω h => FCDet.thr_pos hW0 hWc hxL0 hxR0 h)
  exact isCondFlowLineDriverOn_of_hasSafeLaw_ann h12p h13 hκ h𝒢 hcw hxL hxR hxL0 hxR0 hxLa hxRm hword hW0 hWc hWa
    hhm hc hdom hfwd hliftm hlc hint hseed hT hlaw hmem hG hcc

/-- **The same on a live event `F ∈ 𝒢`** (the form of the supplement's conditional identifications, which hold on the
event that the history reached its entrance: `{T_L < T}` in SB2(1)). All inputs are asked only on `F`: K2's (S) and
(L) with live event `F`, the word, the seed and the conditional chart field almost surely on `F`, integrability under
`P`. Proof: the unconditioned form under `P[·|F]` (`BW1Chain.hasSafeLaw_cond`, `BW1Chain.hasSafeMembers_cond`), whose
regular conditional kernels given `𝒢` agree with those of `P` almost everywhere on `F`
(`BW1Chain.ae_condExpKernel_cond_eq`). -/
theorem isCondFlowLineDriverOn_of_hasSafeLaw_on (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {cw : Ω → BoundaryWord} (hcw : Measurable[𝒢] cw)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω))
    (hword : ∀ᵐ ω ∂P, ω ∈ F → flowLineNL (cw ω).fn (cw ω).jumps 0 = nL ∧
      flowLineNR (cw ω).fn (cw ω).jumps 0 = nR ∧
      truncWord nL nR (padFL κ θ (cw ω).fn (cw ω).jumps) = ((xL ω, xR ω), (ρL, ρR)))
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) φ) P)
    (hseed : ∀ᵐ ω ∂P, ω ∈ F → ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F (FCDet.thr ρL ρR W xL xR) W (geomLW W xL) (geomRW W xR)
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hmem : HasSafeMembers P 𝓗 F (FCDet.thr ρL ρR W xL xR) W
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hG : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
      ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) h' (cw ω₀).fn (cw ω₀).jumps)
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P F h c (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps) W
      (FCDet.thr ρL ρR W xL xR) := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hFm : MeasurableSet F := h𝒢m _ hF
  by_cases hPF : P F = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPF] with ω h1 h2 using absurd h2 h1
  set Q : Measure Ω := ProbabilityTheory.cond P F with hQ
  have : IsProbabilityMeasure Q := ProbabilityTheory.cond_isProbabilityMeasure hPF
  have hker := BW1Chain.ae_condExpKernel_cond_eq (P := P) h𝒢m hF
  have hF0 : MeasurableSet[𝓗 0] F := h𝒢 _ hF
  have hres := isCondFlowLineDriverOn_of_hasSafeLaw (P := Q) h12p h13 hκ h𝒢 hcw hxL hxR hxL0 hxR0 hxLa hxRm
    (BW1Chain.ae_cond_of_ae hFm hword) hW0 hWc hWa hhm hc hdom hfwd hliftm hlc
    (fun φ => BW1Chain.integrable_cond (hint φ)) (BW1Chain.ae_cond_of_ae hFm hseed)
    (BW1Chain.hasSafeLaw_cond hF0 hlaw) (BW1Chain.hasSafeMembers_cond hF0 hmem)
    (BW1Chain.ae_cond_of_ae hFm (by
      filter_upwards [hG, hker] with ω₀ hG₀ hk₀ hω₀
      rw [hk₀ hω₀]
      exact hG₀ hω₀))
    (BW1Chain.ae_cond_of_ae hFm (by
      filter_upwards [hcc, hker] with ω₀ hc₀ hk₀ hω₀
      rw [hk₀ hω₀]
      exact hc₀ hω₀))
  filter_upwards [BW1Chain.ae_of_ae_cond hFm hres, hker] with ω₀ hr hk hω₀
  have h1 := hr hω₀ (mem_univ ω₀)
  rw [hk hω₀] at h1
  exact h1

/-- **SB8's bridge without the input (E)**: K2's inputs in the form produced by the marked Gaussian kernels (Aux.
lemma 77), the mean identification (Aux. lemma 79) and the history-marked locality of the explored union — the
hypotheses `hcond`, `hmean`, `hloc`, `hAK` of `CondDriverBridge.isCondFlowLineDriverOn_of_k2` — on a live event
`F ∈ 𝒢`, for a globally continuous relative driver whose lifetime is the continuation threshold of the geometric
force points of a `𝒢`-measurable word, give the conditional flow line (through `Mean.hasSafeLaw_chartTransport`,
`Mean.hasSafeMembers_chartTransport` and `isCondFlowLineDriverOn_of_hasSafeLaw_on`). The law of the relative driver
is not an input. -/
theorem isCondFlowLineDriverOn_of_markedKernel (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {cw : Ω → BoundaryWord} (hcw : Measurable[𝒢] cw)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω))
    (hword : ∀ᵐ ω ∂P, ω ∈ F → flowLineNL (cw ω).fn (cw ω).jumps 0 = nL ∧
      flowLineNR (cw ω).fn (cw ω).jumps 0 = nR ∧
      truncWord nL nR (padFL κ θ (cw ω).fn (cw ω).jumps) = ((xL ω, xR ω), (ρL, ρR)))
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) φ) P)
    (hseed : ∀ᵐ ω ∂P, ω ∈ F → ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓗𝓜 : ∀ q, 𝓗 q ≤ 𝓜 q) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      (q : ℝ≥0∞) < FCDet.thr ρL ρR W xL xR ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
            ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) q)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ avoidSet W (FCDet.thr ρL ρR W xL xR) ψ q →
        Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (M q ω) ψ =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) q
            (bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω q) z * ψ z)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓗ℋ : ∀ s, 𝓗 s ≤ ℋ s) (hℋ : ∀ s, ℋ s ≤ mΩ)
    (A : ℝ≥0 → Ω → Set ℂ) (hAm : ∀ s, Measurable[mΩ, hittingSigma] (A s))
    (hAc : ∀ s ω, A s ω ⊆ H ∧ IsOpen (H \ A s ω))
    (hloc : ∀ s, WholeField.IsHistoryAvoidanceLocal (ℋ s) (A s) (WholeField.centredField h u₀) P)
    (hAK : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (s : ℝ≥0∞) < FCDet.thr ρL ρR W xL xR ω →
      H \ A s ω = (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) s))
    (hG : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
      ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) h' (cw ω₀).fn (cw ω₀).jumps)
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀) :
    SB.IsCondFlowLineDriverOn κ θ 𝒢 P F h c (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps) W
      (FCDet.thr ρL ρR W xL xR) := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hreg : ∀ᵐ ω ∂P, ω ∈ F → Mean.IsDrvReg W (FCDet.thr ρL ρR W xL xR) ω :=
    Eventually.of_forall fun ω _ => ⟨(hWc ω).continuousOn, hW0 ω⟩
  have hlaw := Mean.hasSafeLaw_chartTransport (ρL := ρL) (ρR := ρR) (VL := geomLW W xL) (VR := geomRW W xR)
    (F := F) h𝒢 hc hdom hfwd hliftm hlc hhm (θ * chiC κ) (chiC κ) 𝓜 h𝓗𝓜 h𝓜 M hcond hmean hreg
  have hmem := Mean.hasSafeMembers_chartTransport (F := F) h𝒢 hhm hu₀ hh0 hc hdom hfwd hliftm hlc hlift
    (θ * chiC κ) (chiC κ) ℋ h𝓗ℋ hℋ A hAm hAc hloc hAK hreg
  exact isCondFlowLineDriverOn_of_hasSafeLaw_on h12p h13 hκ h𝒢 hF hcw hxL hxR hxL0 hxR0 hxLa hxRm hword hW0 hWc
    hWa hhm hc (fun z => h𝒢m _ (hdom z)) (fun z => (hfwd z).mono h𝒢m le_rfl)
    (fun z => (hliftm z).mono h𝒢m le_rfl) hlc hint hseed hlaw hmem hG hcc

end InteractingSLE.Theorem14.SB.Cond
