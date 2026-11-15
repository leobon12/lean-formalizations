/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J6LocalityMarks
import InteractingSLE.Spec.Sec7.Lemma72EMain

/-!
# Wang–Wu at `κ = 4`, (J6): locality of the hulls of the chamber driver for `h_ψ`, also conditionally on `Q`

Packet PROVE-WW-B23. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.24
(text dump L1816–1867): "The conditional field `H = (h|_C) ∘ ψ⁻¹` is a GFF in `ℍ` […]. Proposition 4.20 applies at
every stopping time in the filtration enlarged by the walls. Therefore the transformed middle line `X` satisfies the
local Markov coupling with these values." Item (J6) of the roadmap in `planning/handoffs/PROVE-WW-B20.md`: the hulls
`K_τ` of the chamber driver `W` are local sets of the pulled-back field `h_ψ` at every stopping time `τ < T` of the
chamber filtration (the clause `hloc` of `Chamber4.Chamber4JointStatement`).

The specification's Lemma 7.1 proves this for its pocket conditionally on every event of the exterior record
(PROVE-LEMMA72E, `Sec7.Lemma72E.exists_cond_of_isPocketConstruction`); that proof uses the three-curve space only
through its three-line part and is generic in `κ` and in the seed weights (the weights enter only through the clause's
mean). This file restates it on every three-line space `SeedThree.IsThreeLineSpace` with arbitrary `κ` and weights
`(ρL; ρR)`:

* **`exists_cond_three`**: for a chamber construction `(C, c, γ')` (`Sec7.Lemma71K.IsPocketConstruction`), a
  `σ(β, α)`-measurable branch `n` and the fixed-time chart coupling clause for the prefix filtration `𝓐` of the walls
  and the mapped middle segment (WW-B22's (J5) input), for every event `G` of the exterior record
  `Q = ((β, α), h|_{ℍ ∖ C̄})` (`Sec7.Lemma72B.pocketRecord`) of positive probability, the filtration
  `𝓖_G = usualAugmentation (𝓐 ∨ σ(Q)) P[· | G]` contains `usualAugmentation 𝓐 P` and the `P[· | G]`-null sets, the chart
  coupling clause holds under `P[· | G]` for `𝓖_G`, and the mapped hulls `K_τ` are local sets of `h_ψ = chartField`
  under `P[· | G]` at every stopping time `τ < T` of `𝓖_G`;
* **`isLocalSet_hull_three`** (J6): the case `G = Ω` — the hulls are local sets of `h_ψ` under `P` at every stopping
  time `τ < T` of the chamber filtration `usualAugmentation 𝓐 P`.

Conditional helpers (on the (J5) clause); they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Real

open QuantumZipper (H fwdHull zeroGFFTestCov)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.WangWu.ChamberCond

open LQGMetric Sec7 Sec7.Lemma71C Sec7.Lemma71D Sec7.Lemma71E Sec7.Lemma71K Sec7.Lemma72E Sec6 LocalSets WholeField
  MartChar SeedThree

section Space

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {ρL ρR : Fin 1 → ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

-- mirrored from `Sec7.Lemma72E.exists_cond_of_isPocketConstruction`
/-- **The chamber coupling conditionally on the exterior record, on a three-line space** (see the module docstring).
-/
theorem exists_cond_three (hS : IsThreeLineSpace P h u₀ β α γ) (hpc : IsPocketConstruction P β α γ C c γ')
    {n : Ω → ℤ} (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' k : ℝ}
    (hcf : IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) a' k h)
    (G : Set Ω) (hG : MeasurableSet[MeasurableSpace.comap
      (Lemma72B.pocketRecord β α (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ)) h) inferInstance] G)
    (hPG : P G ≠ 0) :
    ∃ 𝓖G : Filtration ℝ≥0 mΩ, 𝓖G.IsRightContinuous ∧
      usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P ≤ 𝓖G ∧
      (∀ s, MeasurableSet s → P[|G] s = 0 → MeasurableSet[𝓖G 0] s) ∧
      Coupling.MartMeans2.IsChartCouplingCharFun κ ρL ρR (P[|G]) 𝓖G (fun s ω => segDriver (γ' ω) s)
        (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL) (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR)
        (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) a' k h ∧
      ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖G τ → (∀ᵐ ω ∂(P[|G]), (τ ω : ℝ≥0∞) < capLife (γ' ω)) →
        IsLocalSet (fun ω => fwdHull (fun s : ℝ => segDriver (γ' ω) s.toNNReal) ((τ ω).untopD 0 : ℝ≥0))
          (fun ω => chartField (shiftLift (c ω) (n ω)) a' k (h ω)) (P[|G]) := by
  -- the objects
  have hh : Measurable h := hS.1
  have hu₀ := hS.2.1
  have hh0 := hS.2.2.1
  have hS' := hS
  obtain ⟨-, -, -, hβ62, hα62, -, -⟩ := hS'
  have hpc' := hpc
  obtain ⟨hC, hCm, hconf, hdom, hfm, hlm, hlc, -, -, -, hseg, -, -⟩ := hpc'
  set 𝓐 := prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' with h𝓐def
  set W : ℝ≥0 → Ω → ℝ := fun s ω => segDriver (γ' ω) s with hWdef
  set T : Ω → ℝ≥0∞ := fun ω => capLife (γ' ω) with hTdef
  set c' : Ω → Chart := fun ω => shiftLift (c ω) (n ω) with hc'def
  have hcc' : ∀ ω, (c' ω).IsConformal := fun ω => isConformal_shiftLift (hconf ω) (n ω)
  have hlc' : ∀ ω, ContinuousOn (c' ω).2.2 (c' ω).dom := fun ω => continuousOn_shiftLift (hlc ω) (n ω)
  have hlift' : ∀ ω, InnerProductSpace.HarmonicOnNhd (c' ω).2.2 (c' ω).dom := harmonicOnNhd_shiftLift hpc n
  have hWc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun ω =>
    (hseg ω).segDriver_spec.2.1
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => (hseg ω).segDriver_spec.1
  have hWa : AdaptedBefore 𝓐 T W := adaptedBefore_three hS hpc
  have hTm : ∀ t : ℝ≥0, MeasurableSet[𝓐 t] {ω | (t : ℝ≥0∞) < T ω} := measurableSet_lt_capLife_three hS hpc
  have h₀ : ∀ t, MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ 𝓐 t := fun t =>
    le_prefixFiltrationOf (comap_pair_le_three hS) γ' t
  -- the chart is a function of the walls
  have hdomm : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (c' ω).dom} := fun z => by
    have e : {ω | z ∈ (c' ω).dom} = {ω | z ∈ C ω} := by
      ext ω
      show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
      rw [hdom ω]
    rw [e]
    exact @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C (fun ω => (hC ω).1) hCm z
  have hfm' : ∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).1 z) := hfm
  have hlm' : ∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).2.2 z) := fun z =>
    @measurable_indicator_shiftLift Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) c n hn z
      (hdomm z) (hlm z)
  have hCm' : ∀ (z : ℂ) (r : ℝ), MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | closedBall z r ⊆ ((c' ω).dom : Set ℂ)} := fun z r => by
    have := measurableSet_closedBall_dom hpc z r
    exact this
  have hclos : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω))
      inferInstance] {ω | Disjoint (tsupport φ) (closure ((c' ω).dom : Set ℂ))} := fun φ =>
    @Lemma72B.measurableSet_disjoint_closure_of_mem Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
      (fun ω => ((c' ω).dom : Set ℂ)) (fun ω => (c' ω).dom.isOpen) hdomm _ φ.hasCompactSupport
  -- the exterior record
  set Q := Lemma72B.pocketRecord β α (fun ω => ((c' ω).dom : Set ℂ)) h with hQdef
  have hβα : Measurable fun ω => (β ω, α ω) :=
    (measurable_pi_iff.2 hβ62.2.2.2.1).prodMk (measurable_pi_iff.2 hα62.2.2.2.1)
  have hQm : Measurable Q :=
    Lemma72B.measurable_pocketRecord hβ62.2.2.2.1 hα62.2.2.2.1 hh fun φ => hβα.comap_le _ (hclos φ)
  have h𝒬 : MeasurableSpace.comap Q inferInstance ≤ mΩ := hQm.comap_le
  -- the marks of (R2′)
  choose ℋ hℋle hℋloc hℋ𝓐 using fun t : ℝ≥0 => exists_marks_three (h := h) (u₀ := u₀) hS hpc t
  have hBm : ∀ t : ℝ≥0, Measurable[mΩ, hittingSigma] (markedSet W T c t) := fun t =>
    (measurable_markedSet_three hS hpc t).mono (𝓐.le t) le_rfl
  have hσℋ : ∀ t, MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ ℋ t := fun t =>
    (h₀ t).trans (hℋ𝓐 t)
  set 𝒢 : ℝ≥0 → MeasurableSpace Ω := fun t => germSigma (markedSet W T c t) (centredField h u₀) ⊔ ℋ t
    with h𝒢def
  have h𝒢le : ∀ t, 𝒢 t ≤ mΩ := fun t =>
    sup_le (germSigma_le (hBm t) (measurable_centredField hh u₀)) (hℋle t)
  have h𝓐𝒢 : ∀ t, 𝓐 t ≤ 𝒢 t := fun t => (hℋ𝓐 t).trans le_sup_right
  have h𝒬𝒢 : ∀ t, MeasurableSpace.comap Q inferInstance ≤ 𝒢 t := fun t => by
    have hβm : ∀ s, Measurable[ℋ t] fun ω => β ω s := fun s =>
      (((measurable_pi_apply s).comp measurable_fst).comp (comap_measurable _)).mono (hσℋ t) le_rfl
    have hαm : ∀ s, Measurable[ℋ t] fun ω => α ω s := fun s =>
      (((measurable_pi_apply s).comp measurable_snd).comp (comap_measurable _)).mono (hσℋ t) le_rfl
    exact Lemma72C.comap_pocketRecord_le (ℋ := ℋ t) (B := markedSet W T c t)
      (fun ω => H_diff_dom_subset_markedSet (hcc' ω)) hβm hαm (h := h) (smoothDist upperHalfPlaneOpens u₀)
      fun φ => hσℋ t _ (hclos φ)
  -- the clause under `P[· | G]`
  have hmod : ∀ t φ, ∀ᵐ ω ∂P, ω ∈ Lemma72D.clauseEvent W T c' t φ →
      ‖P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝒢 t] ω‖ =
        Real.exp (-(1 / 2) * zeroGFFTestCov ((c' ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)))
          φ φ) := by
    intro t φ
    filter_upwards [Lemma72D.norm_condExp_cexp_of_isHistoryAvoidanceLocal hh hh0 (hBm t) (hℋle t) (hℋloc t)
      (ae_of_all _ fun ω => ⟨markedSet_subset, isOpen_H_diff_markedSet (hconf ω) (hWc ω)⟩) φ] with ω hω hE
    rw [hω, H_diff_markedSet_of_lt (hconf ω) hE.1]
    rfl
  have hcov : ∀ t φ, ∃ E : ℕ → Set Ω, (∀ j, MeasurableSet[𝓐 t] (E j)) ∧
      (∀ j, E j ⊆ Lemma72D.clauseEvent W T c' t φ) ∧ Lemma72D.clauseEvent W T c' t φ ⊆ ⋃ j, E j := fun t φ =>
    Lemma72D.exists_cover_clauseEvent hcc' hCm' hfm' hWa hWc t (h₀ t) (hTm t) φ
  have hcfG := Lemma72D.isChartCouplingCharFunConst_cond hh h𝒬 𝒢 h𝒢le h𝓐𝒢 h𝒬𝒢 hmod hcov hcf hG hPG
  have hμ : IsProbabilityMeasure (P[|G]) := cond_isProbabilityMeasure hPG
  have hac : P[|G] ≪ P := cond_absolutelyContinuous
  set 𝓗 := Lemma72D.supConst 𝓐 (MeasurableSpace.comap Q inferInstance) h𝒬 with h𝓗def
  have hcfμ : Coupling.MartMeans2.IsChartCouplingCharFun κ ρL ρR (P[|G]) (usualAugmentation 𝓗 (P[|G])) W
      (geomL W LP.twoSeedXL) (geomR W LP.twoSeedXR) T c' a' k h :=
    isChartCouplingCharFun_usualAugmentation hh hcc' hlc' hWc (fun i ω => continuousOn_geomL hWc LP.twoSeedXL i ω)
      (fun i ω => continuousOn_geomR hWc LP.twoSeedXR i ω)
      (fun ω t ht => geomL_le_le_geomR hWc LP.twoSeedXL LP.twoSeedXR ht) hcfG
  refine ⟨usualAugmentation 𝓗 (P[|G]), Ito.isRightContinuous_usualAugmentation 𝓗 (P[|G]),
    Lemma72D.usualAugmentation_le_cond _ 𝓐 h𝒬 G, fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0,
    hcfμ, ?_⟩
  -- locality under `P[· | G]`
  intro τ hτ hτT
  have hψω : ∀ ω, chartField (c' ω) a' k (h ω) = Chart.chartTransport (hcc' ω) 1 a' k (h ω) := fun ω =>
    dite_eq_left (hcc' ω)
  have hψe : (fun ω => chartField (shiftLift (c ω) (n ω)) a' k (h ω)) =
      fun ω => Chart.chartTransport (hcc' ω) 1 a' k (h ω) := funext hψω
  have ht : ∀ ω, IsChartTransport (c' ω) 1 a' k (h ω) (Chart.chartTransport (hcc' ω) 1 a' k (h ω)) := fun ω => by
    have := isChartTransport_chartField (hcc' ω) (hlc' ω) a' k (h ω)
    rwa [hψω ω] at this
  rw [hψe]
  -- the σ-algebras at time `0` of `𝓖_G`
  have h0G : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ usualAugmentation 𝓗 (P[|G]) 0 :=
    (h₀ 0).trans ((Lemma72D.le_supConst 𝓐 _ h𝒬 0).trans (Ito.le_usualAugmentation 𝓗 (P[|G]) 0))
  have hψm : Measurable fun ω => Chart.chartTransport (hcc' ω) 1 a' k (h ω) :=
    Chart.measurable_chartTransport_random' hcc' (fun z => (comap_pair_le_three hS) _ (hdomm z))
      (fun z => (hfm' z).mono (comap_pair_le_three hS) le_rfl)
      (fun z => (hlm' z).mono (comap_pair_le_three hS) le_rfl) hlc' hh 1 a' k
  -- the centred field is a zero-boundary GFF under `P[· | G]`
  obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR (fun _ : Fin 1 => (0 : ℝ))
    (fun _ : Fin 1 => (0 : ℝ))
  have hu₀'c : ContinuousOn u₀' H := fun z hz => ((hu₀'.1 z hz).1.continuousAt).continuousWithinAt
  have hcpl := Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hcc' (fun z => h0G _ (hdomm z))
    (fun z => (hfm' z).mono h0G le_rfl) (fun z => (hlm' z).mono h0G le_rfl) hlc' hh
    (Eventually.of_forall fun ω => ⟨hW0 ω, hWc ω⟩) hcfμ ht
  have hzb := Lemma71J.isZBGFFProcess_of_isCouplingCharFun hcpl hψm
    (Eventually.of_forall fun ω => ⟨bot_le.trans_lt ((hseg ω).ofReal_capClock_lt zero_le_one), hWc ω, hW0 ω,
      fun i => geomL_twoSeed_zero_of (hW0 ω) i, fun i => geomR_twoSeed_zero_of (hW0 ω) i⟩) hu₀'
  have hX := Coupling.isZeroBoundaryGFF_sub_smoothDist hψm hu₀'c hzb
  -- the kernels at rational times
  have hu₀'h := Coupling.isHarmonicDistOn_smoothDist_of hu₀'
  have hker0 : ∀ s : ℚ≥0, ∃ Ms : Ω → DistOn upperHalfPlaneOpens,
      (∀ᵐ ω ∂P, IsHarmonicDistOn (Ms ω) (openPart W T (s : ℝ≥0) ω)) ∧
      ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂(P[|G]),
        (P[|G])[fun ω' => Complex.exp (Complex.I *
          ((Chart.chartTransport (hcc' ω') 1 a' k (h ω') - smoothDist upperHalfPlaneOpens u₀') χ : ℂ)) |
            𝒢 (s : ℝ≥0)] ω = rangeKerCF (Ms ω) (openPart W T (s : ℝ≥0) ω) χ := by
    intro s
    obtain ⟨Ms, hMh, hMk⟩ := exists_condExp_cexp_chartTransport_cond (ℋ := ℋ (s : ℝ≥0)) hh hu₀.1 hh0 hcc'
      (fun z => hσℋ _ _ (hdomm z)) (fun z => (hfm' z).mono (hσℋ _) le_rfl)
      (fun z => (hlm' z).mono (hσℋ _) le_rfl) hlc' hlift' (O := openPart W T (s : ℝ≥0))
      (fun ω => isOpen_openPart (hWc ω)) (fun ω => openPart_subset) (hℋle _) (hBm _) (hℋloc _) a' k hu₀'h
    exact ⟨Ms, hMh, fun χ => hMk G (h𝒬𝒢 _ G hG) hPG χ⟩
  choose Mk hMkh hMkk using hker0
  have hloc := Lemma72D.isLocalSet_hull_of_kernels (P := P[|G]) (𝓗 := 𝓗) (W := W) (ζ := T)
    (𝒦 := fun s : ℚ≥0 => 𝒢 (s : ℝ≥0)) (M := Mk) (V := fun s : ℚ≥0 => openPart W T (s : ℝ≥0)) hX
    (Ito.adaptedBefore_mono (Lemma72D.le_supConst 𝓐 _ h𝒬) hWa) (Eventually.of_forall fun ω => ⟨hWc ω, hW0 ω⟩)
    (fun s => h𝒢le _) hMkk ?_ ?_ ?_ hτ hτT
  · have := Coupling.IsLocalSet.add_dist hloc hu₀'h
    simpa only [sub_add_cancel] using this
  · -- the kernel domains
    intro s
    filter_upwards [hac.ae_le (hMkh s)] with ω hω hlt
    rw [openPart_of_lt (ζ := T) (ω := ω) hlt] at hω ⊢
    exact ⟨Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath (hWc ω) hlt, sdiff_subset, subset_rfl, hω⟩
  · -- the events of `𝓖_G` before `s`
    intro r s hrs D hD
    obtain ⟨D', hD', hDD'⟩ := Ito.exists_ae_eq_of_measurableSet_usualAugmentation
      (show (r : ℝ≥0) < (s : ℝ≥0) by exact_mod_cast hrs) hD
    exact ⟨D', (sup_le (h𝓐𝒢 _) (h𝒬𝒢 _) : 𝓗 (s : ℝ≥0) ≤ 𝒢 (s : ℝ≥0)) D' hD', hDD'⟩
  · -- the safety events
    intro s F hFH
    exact ⟨_, h𝓐𝒢 _ _ (Lemma72D.measurableSet_lt_disjoint_ballsK hWa hWc (s : ℝ≥0) (hTm _) hFH),
      EventuallyEq.rfl⟩

/-- **(J6): the hulls of the chamber driver are local sets of `h_ψ`** (Wang–Wu Proposition 4.24, "Proposition 4.20
applies at every stopping time in the filtration enlarged by the walls"). On a three-line space with a chamber
construction, a `σ(β, α)`-measurable branch and the fixed-time chart coupling clause, the mapped hulls `K_τ` are local
sets of `h_ψ = chartField` at every stopping time `τ < T` of the chamber filtration `usualAugmentation 𝓐 P`
(`exists_cond_three` at `G = Ω`). Conditional helper (on the (J5) clause). -/
theorem isLocalSet_hull_three (hS : IsThreeLineSpace P h u₀ β α γ) (hpc : IsPocketConstruction P β α γ C c γ')
    {n : Ω → ℤ} (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' k : ℝ}
    (hcf : IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) a' k h)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P) τ)
    (hτT : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < capLife (γ' ω)) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => segDriver (γ' ω) s.toNNReal) ((τ ω).untopD 0 : ℝ≥0))
      (fun ω => chartField (shiftLift (c ω) (n ω)) a' k (h ω)) P := by
  have hPuniv : P univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  obtain ⟨𝓖U, -, hle, -, -, hlocU⟩ := exists_cond_three hS hpc hn hcf univ MeasurableSet.univ hPuniv
  have hτU : IsStoppingTime 𝓖U τ := fun i => hle i _ (hτ i)
  have hloc := hlocU τ hτU (by rwa [cond_univ])
  rwa [cond_univ] at hloc

end Space

end InteractingSLE.WangWu.ChamberCond
