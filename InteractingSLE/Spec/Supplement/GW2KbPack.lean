/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxSamp

/-!
# Claim(k)'s base (GEOM2 round 12): STAGEMEAN's kernel route with the counterflow word given

Packet PROVE-GW2-GEOM2, round 12. `GW2Omx.kernel_launch_mean` returns its counterflow word `c'` existentially (the
word is chosen inside `GW2Olm.counterflow_pack` by `BoundaryWord.exists_fn_eq`). The base of Claim(k) compares the
kernel word with the word `cw` of the top's word map `baseWm cw`, so the word must be the given one. This file
re-runs the three steps with the word as an input:

* `IsCfWordOf` (a word of the boundary data of the counterflow's field), `exists_isCfWordOf`;
* **`counterflow_packW`**, **`kernel_meansNW`**, **`kernel_launch_meanW`**: `GW2Olm.counterflow_pack`,
  `GW2Omx.kernel_meansN`, `GW2Omx.kernel_launch_mean` with the word `c'` given (same proofs).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Kb

open Restart Exist Exist.StagedLaw WholeField LocalSets Sec7.PocketTraversal Supp8 Supp8.GB6 Supp8.GB6LineL
  Supp8.GB6LMean Supp8.Q3Chain RelSafeS GW2JointKernel GW2TipSystem GW2Fb GW2JDetR8 GW2Omx
open Supp8.Q3Rel (invHull relLog)
open QuantumZipper (fwdMap logDerivFwd)
open QuantumZipper (fwdHull)

/-- **A word of the counterflow's boundary data**: the counterflow `W` is a flow line of angle `0` of the
infinity-source transport `h'` of `X` with data `(b', J')`, and the word `c'` has jump set `J'` and function `b'` off
it. -/
def IsCfWordOf {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (μ : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (c' : BoundaryWord) : Prop :=
  ∃ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens), IsPiecewiseConstantBoundaryData b' J' ∧
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (X ω) (h' ω)) ∧
    IsFlowLineDriver (16 / κ) b' J' 0 μ h' W ζ ∧ c'.jumps = J' ∧ ∀ y ∉ J', c'.fn y = b' y

theorem IsCfWordOf.isCenteredCounterflowDriver {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {μ : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c' : BoundaryWord}
    (h : IsCfWordOf κ μ X W ζ c') : IsCenteredCounterflowDriver κ μ X W ζ := by
  obtain ⟨b', J', h', hb', hT, hfl, -, -⟩ := h
  exact ⟨b', J', h', hb', hT, hfl⟩

/-- Every centred counterflow has a word of its data. -/
theorem exists_isCfWordOf {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {μ : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ μ X W ζ) :
    ∃ c' : BoundaryWord, IsCfWordOf κ μ X W ζ c' := by
  obtain ⟨b', J', h', hb', hT, hfl⟩ := hcf
  obtain ⟨c', hc'J, hc'b⟩ := BoundaryWord.exists_fn_eq hb'
  exact ⟨c', b', J', h', hb', hT, hfl, hc'J, hc'b⟩

/-- **`GW2Olm.counterflow_pack` with the counterflow word given.** -/
theorem counterflow_packW (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → DistOn upperHalfPlaneOpens}
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData μ X b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c' : BoundaryWord} (hc' : IsCfWordOf κ μ X W ζ c')
    (hζ : ∀ᵐ ω ∂μ, ζ ω = ⊤) :
    ∃ (h' h₁ : Ω → DistOn upperHalfPlaneOpens) (𝓕' : Filtration ℝ≥0 mΩ)
      (VL' : Fin (flowLineNL c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ) (VR' : Fin (flowLineNR c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ)
      (B' : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ) (_hX' : IsMeasurableKilledDriving W VL' VR' ζ),
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (X ω) (h' ω)) ∧
      (∀ ω, IsTranslateAddConst 0 (0 * chiC (16 / κ)) (h' ω) (h₁ ω)) ∧
      IsOptionalHullCoupling (16 / κ) (flowLineXL c'.fn c'.jumps 0) (flowLineXR c'.fn c'.jumps 0)
        (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0) (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) μ 𝓕' W VL' VR' B' ζ h₁ ∧
      (∀ᵐ ω ∂μ, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) ∧
      (∀ᵐ ω ∂μ, ∀ v : ℝ≥0, 0 < v → γ ω v ≠ 0) := by
  classical
  have hcf : IsCenteredCounterflowDriver κ μ X W ζ := hc'.isCenteredCounterflowDriver
  obtain ⟨b', J', h', hb', hT, hfl, hc'J, hc'b⟩ := id hc'
  have hc'pc : IsPiecewiseConstantBoundaryData c'.fn c'.jumps := BoundaryWord.isPiecewiseConstantBoundaryData c'
  have hfl' : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 μ h' W ζ :=
    (StagedLaw.isFlowLineDriver_congr_of_eqOn hb' hc'pc J' (fun y hy => by rw [hc'J] at *; exact hc'b y hy)).2 hfl
  obtain ⟨h₁, 𝓕', VL', VR', B', htr', hC'⟩ := hfl'
  set γ : Ω → ℝ≥0 → ℂ := fun ω =>
    if h : ∃ g : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ g then h.choose else 0 with hγ
  have hreg := GW2Later.ae_counterflow_regular h13 hκ hcf hζ
  have hcomp : ∀ᵐ ω ∂μ, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hζ, hreg] with ω hζω hrω
    obtain ⟨g, hg, -⟩ := hrω
    have hex : ∃ g : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ g := ⟨g, hg⟩
    refine ⟨hζω, ?_⟩
    simp only [hγ, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hNR : ∀ᵐ ω ∂μ, ∀ v : ℝ≥0, 0 < v → γ ω v ≠ 0 := by
    have hn := GW2Rd.counterflowNoReturn_of_thm13 h13 κ hκ hκ4 b J hb μ X hG W ζ hcf hζ
    filter_upwards [hn, hcomp] with ω hnω hc v hv
    exact hnω (γ ω) hc.2 v hv
  exact ⟨h', h₁, 𝓕', VL', VR', B', γ, hC'.2.2.2.1, hT, htr', hC', hcomp, hNR⟩


/-- **`GW2Omx.kernel_meansN` with the counterflow word given.** -/
theorem kernel_meansNW (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hG : IsGFFWithBoundaryData μ X b J) {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞}
    {c' : BoundaryWord} (hc' : IsCfWordOf κ μ X Wk ζk c') {W' : ℝ≥0 → Ω → ℝ}
    (hW' : ∀ᵐ ω ∂μ, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ')
    {cL : Chart} (hpb : GW1P.HasProperBdryExt cL) {ℓ : Ω → ℝ≥0 → ℝ≥0} {Aset : Set ℂ}
    (hd : ∀ᵐ ω ∂μ, ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
      range (ℓ ω) = {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) Aset} ∧
      ∀ (r : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z ↔
        infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z)
    (s : ℝ≥0) {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b J θ μ X Wα ζα)
    {α : Ω → ℝ≥0 → ℂ} (hα : ∀ᵐ ω ∂μ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
      (flowLineXL b J 0) (flowLineXR b J 0)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    ∃ (σ : ℕ → Ω → WithTop ℝ≥0) (Xθ : Ω → DistOn upperHalfPlaneOpens) (T : ℕ → Ω → ℝ≥0)
      (γ : Ω → ℝ≥0 → ℂ),
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (X ω) (Xθ ω)) ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField Xθ u₀) μ ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → ∃ n, t ≤ T n ω) ∧
      (∀ᵐ ω ∂μ, ∀ n, (T n ω : ℝ≥0∞) < ζα ω) ∧
      (∀ᵐ ω ∂μ, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
      ∀ N : ℕ, (∀ ω, σ N ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)) ∧
        (∀ᵐ ω ∂μ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < (N : ℝ≥0) → σ N ω = (t₀ : WithTop ℝ≥0)) ∧
        (∀ᵐ ω ∂μ, σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0) → ∃ q : ℝ≥0, s < ℓ ω q) ∧
        (∀ᵐ ω ∂μ, σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0) → ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < (N : ℝ≥0)) ∧
        (∃ 𝓝 : {m : MeasurableSpace Ω // m ≤ mΩ}, MeasurableSet[𝓝.1] {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} ∧
          RetMeanLocAt κ θ μ Xθ c' Wk ζk (σ N) u₀ 𝓝) ∧
        ∀ (n : ℕ) (t : ℝ≥0), ∃ 𝓝 : {m : MeasurableSpace Ω // m ≤ mΩ},
          MeasurableSet[𝓝.1] {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} ∧
          MeasurableSet[𝓝.1] {ω | (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)} ∧
          UnionMeanLocAt κ θ μ Xθ b J c' Wk ζk (σ N) Wα α γ (fun ω => min (t : WithTop ℝ≥0) (T n ω)) u₀ 𝓝 := by
  have hcf : IsCenteredCounterflowDriver κ μ X Wk ζk := hc'.isCenteredCounterflowDriver
  obtain ⟨h', h₁, 𝓕', VL', VR', B', γ, hX', hT, htr', hC', hcomp, hNR⟩ :=
    counterflow_packW h13 hκ hκ4 hb hG hc' (hd.mono fun _ h => h.1)
  have hst := fun N : ℕ => exists_stop_of_datum_ext2 h13 hκ μ hcf hX' hW' hpb hd s (N : ℝ≥0)
  choose σ hσ hσt hσN hσeq hσconv hσlt using hst
  obtain ⟨Xθ, 𝓕, VL, VR, B, hX, T, htr, hC, hTa⟩ := GW2Olm.flowLine_pack hκ hfl hseed
  refine ⟨σ, Xθ, T, γ, htr, isZeroBoundaryGFF_centredField hC hu₀, hTa.2.2.2, ae_all_iff.2 hTa.2.2.1, hcomp,
    fun N => ?_⟩
  have hσζ : ∀ᵐ ω ∂μ, (σ N ω : ℝ≥0∞) < ζk ω := by
    filter_upwards [hcomp] with ω hc
    rw [hc.1]
    exact lt_top_iff_ne_top.2 (hσt N ω)
  obtain ⟨A, -, hAG, hAe, hAst, hAd, hlocA, -, hmeanA⟩ :=
    GW2Stm.exists_retained_gw2_stop h12 h13 hκ hb hG hT htr' hC' hX' (hσ N) (hσt N) hσζ htr hu₀
  refine ⟨hσN N, hσeq N, hσconv N, hσlt N, ⟨⟨(hσ N).measurableSpace, (hσ N).measurableSpace_le⟩,
    (hσ N).measurableSet_lt' (N : ℝ≥0), A, hAst, hAG, hAe, hlocA, hAd, hmeanA⟩, fun n t => ?_⟩
  have hτ : IsStoppingTime (drivingFiltration μ hX) (fun ω => min (t : WithTop ℝ≥0) (T n ω)) :=
    (isStoppingTime_const _ t).min (hTa.1 n)
  have hτζ : ∀ᵐ ω ∂μ, ((min (t : WithTop ℝ≥0) (T n ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζα ω :=
    (hTa.2.2.1 n).mono fun _ hω => (min_le_right _ _).trans_lt hω
  have hτt : ∀ ω, min (t : WithTop ℝ≥0) (T n ω) ≠ ⊤ :=
    fun _ => ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  refine ⟨⟨(hσ N).measurableSpace ⊔ hτ.measurableSpace, sup_le (hσ N).measurableSpace_le hτ.measurableSpace_le⟩,
    le_sup_left (a := (hσ N).measurableSpace) _ ((hσ N).measurableSet_lt' (N : ℝ≥0)), ?_, ?_⟩
  · refine le_sup_right (a := (hσ N).measurableSpace) _ ?_
    have e : {ω | (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)} =
        {ω | min (t : WithTop ℝ≥0) (T n ω) < (t : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
    rw [e]
    exact (hτ.measurableSet_lt' t).compl
  · exact exists_unionMean_gw2_stop_loc h12 h13 hκ hb hG hT htr' hC' hX' hcomp hNR (hσ N) (hσt N) htr hC hα hX
      hτ hτζ hτt hu₀


/-- **`GW2Omx.kernel_launch_mean` with the counterflow word given** (one probability measure). -/
theorem kernel_launch_meanW (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [mΩ : MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hG : IsGFFWithBoundaryData ν X b J) {u' : ℂ → ℝ} (hu' : IsBoundedHarmonicExtension b J u')
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} {c' : BoundaryWord} (hc' : IsCfWordOf κ ν X Wk ζk c') {W' : ℝ≥0 → Ω → ℝ}
    (hW' : ∀ᵐ ω ∂ν, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ')
    {cL : Chart} (hpb : GW1P.HasProperBdryExt cL) {ℓ : Ω → ℝ≥0 → ℝ≥0} {Aset : Set ℂ}
    (hd : ∀ᵐ ω ∂ν, ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
      range (ℓ ω) = {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) Aset} ∧
      ∀ (r : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z ↔
        infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z)
    (s : ℝ≥0) {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b J θ ν X Wα ζα)
    {α : Ω → ℝ≥0 → ℂ} (hα : ∀ᵐ ω ∂ν, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
      (flowLineXL b J 0) (flowLineXR b J 0)) {uθ : ℂ → ℝ}
    (huθ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uθ)
    (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}) {L : Ω → Set ℂ} (hLm : Measurable[𝓜.1, hittingSigma] L)
    (hLc : ∀ ω, L ω ⊆ H ∧ IsOpen (H \ L ω)) (hLl : IsHistoryAvoidanceLocal 𝓜.1 L (centredField X u') ν)
    {m : Ω → DistOn upperHalfPlaneOpens} (hmh : ∀ᵐ ω ∂ν, IsHarmonicDistOn (m ω) (H \ L ω))
    (hk : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (centredField X u' ω ψ : ℂ)) | 𝓜.1] =ᵐ[ν]
        fun ω => rangeKerCF (m ω) (H \ L ω) ψ)
    {I : Set Ω} (hI : MeasurableSet[𝓜.1 ⊔ Ito.nullSets ν] I) (t : ℝ≥0)
    (hsub : ∀ᵐ ω ∂ν, ω ∈ I → ∃ t₀ : ℝ≥0, ℓ ω t₀ = s ∧ ∀ v ≤ t₀, ∀ u ≤ t, (u : ℝ≥0∞) < ζα ω →
      invHull (fun r : ℝ => Wk r.toNNReal ω) (v : ℝ) ∪ fwdHull (fun r : ℝ => Wα r.toNNReal ω) (u : ℝ) ⊆ L ω)
    (heq : ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → (t : ℝ≥0∞) < ζα ω → ω ∈ I ∧
      L ω = invHull (fun r : ℝ => Wk r.toNNReal ω) (t₀ : ℝ) ∪ fwdHull (fun r : ℝ => Wα r.toNNReal ω) (t : ℝ)) :
    ∃ (Xθ : Ω → DistOn upperHalfPlaneOpens) (γ : Ω → ℝ≥0 → ℂ),
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (X ω) (Xθ ω)) ∧
      (∀ᵐ ω ∂ν, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
      ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → (t : ℝ≥0∞) < ζα ω → γ ω t₀ ∈ H → 0 < t →
        ((t : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
          ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 t₀) →
        ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, w z * φ z) →
          UnionFormAt κ θ b J c' Wk ζk Wα uθ ω t₀ t w (H \ L ω) := by
  classical
  obtain ⟨σ, Xθ, T, γ, htr, hzθ, hcov, hTζ, hcomp, hN⟩ :=
    kernel_meansNW h12 h13 hκ hκ4 hb hG hc' hW' hpb hd s hfl hα hseed huθ
  have hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u') ν :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hG hu'
  have hcent : centredField Xθ uθ = centredField X u' := centredField_translate_eq htr hzθ hh
  refine ⟨Xθ, γ, htr, hcomp, ?_⟩
  have hmin : ∀ (a b : ℝ≥0), min (a : WithTop ℝ≥0) (b : WithTop ℝ≥0) = ((min a b : ℝ≥0) : WithTop ℝ≥0) :=
    fun a b => (WithTop.coe_min a b).symm
  have key : ∀ N n : ℕ, ∀ᵐ ω ∂ν, ω ∈ {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} ∩
      {ω | (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)} →
      (γ ω ((σ N ω).untopD 0 : ℝ≥0) ∈ H ∧ 0 < (min (t : WithTop ℝ≥0) (T n ω)).untopD 0 ∧
        (((min (t : WithTop ℝ≥0) (T n ω)).untopD 0 : ℝ≥0) : ℝ≥0∞) <
          firstContactTime (fun u => (α ω u : OnePoint ℂ))
            ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ N ω).untopD 0 : ℝ≥0))) →
      ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, w z * φ z) →
        UnionFormAt κ θ b J c' Wk ζk Wα uθ ω ((σ N ω).untopD 0) ((min (t : WithTop ℝ≥0) (T n ω)).untopD 0) w
          (H \ L ω) := by
    intro N n
    obtain ⟨hσN, hσeq, hσconv, hσlt, -, hU⟩ := hN N
    obtain ⟨𝓝, hG1, hG2, hUN⟩ := hU n t
    obtain ⟨A, K, hAm, hKm, hAe, hKe, hUc, hUl, hUm, hdet, hmean⟩ := hUN.form
    rw [hcent] at hUl hdet hmean
    refine ae_eqOn_launchMean_of_kernel hh 𝓜.2 𝓝.2 hLm hLc hLl hmh hk hUm hUc hUl hdet hI ?_ (hG1.inter hG2) ?_
      hmean
    · filter_upwards [hsub, hAe, hKe, hσeq, hTζ] with ω hs hA hK hσe hT hωI
      obtain ⟨t₀, ht₀, hall⟩ := hs hωI
      rw [hA, hK]
      refine hall _ ?_ _ ?_ ?_
      · rcases lt_or_ge t₀ (N : ℝ≥0) with h | h
        · rw [hσe t₀ ht₀ h, WithTop.untopD_coe]
        · obtain ⟨v, hv⟩ : ∃ v : ℝ≥0, σ N ω = (v : WithTop ℝ≥0) :=
            WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hσN ω)) |>.imp fun _ h => h.symm
          rw [hv, WithTop.untopD_coe]
          have := hσN ω
          rw [hv, WithTop.coe_le_coe] at this
          exact this.trans h
      · rw [hmin, WithTop.untopD_coe]
        exact min_le_left _ _
      · rw [hmin, WithTop.untopD_coe]
        exact (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt (hT n)
    · filter_upwards [heq, hσconv, hσlt, hσeq, hAe, hKe, hd, hTζ] with ω he hc hlt hσe hA hK hdω hT hωG
      obtain ⟨h1, h2⟩ := hωG
      obtain ⟨q, hq⟩ := hc h1
      have hℓ0 : ℓ ω 0 = 0 := GW2Sgk.clock_zero_of_range hdω.2.2.1 hdω.2.2.2.1
      obtain ⟨t₀, -, ht₀⟩ := intermediate_value_Icc (zero_le (a := q)) hdω.2.1.continuousOn
        ⟨by rw [hℓ0]; exact zero_le, hq.le⟩
      have htN := hlt h1 t₀ ht₀
      have hσv := hσe t₀ ht₀ htN
      have htT : t ≤ T n ω := by
        have h2' : (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω) := h2
        rw [hmin, WithTop.coe_le_coe] at h2'
        exact h2'.trans (min_le_right _ _)
      have htζ : (t : ℝ≥0∞) < ζα ω := (ENNReal.coe_le_coe.2 htT).trans_lt (hT n)
      obtain ⟨hωI, hL⟩ := he t₀ ht₀ htζ
      refine ⟨hωI, ?_⟩
      rw [hL, hA, hK, hσv, WithTop.untopD_coe, hmin, WithTop.untopD_coe, min_eq_left htT]
  have hσeqAll : ∀ᵐ ω ∂ν, ∀ N : ℕ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < (N : ℝ≥0) → σ N ω = (t₀ : WithTop ℝ≥0) :=
    ae_all_iff.2 fun N => (hN N).2.1
  filter_upwards [ae_all_iff.2 fun N => ae_all_iff.2 fun n => key N n, hcov, hσeqAll] with ω hall hcovω hσω
  intro t₀ ht₀ htζ hγH ht0 hfc w hw hpair
  obtain ⟨N, hN'⟩ := exists_nat_gt t₀
  obtain ⟨n, hn⟩ := hcovω t htζ
  have hσv : σ N ω = (t₀ : WithTop ℝ≥0) := hσω N t₀ ht₀ hN'
  have hτv : min (t : WithTop ℝ≥0) (T n ω) = (t : WithTop ℝ≥0) := by rw [hmin, min_eq_left hn]
  have hmem : ω ∈ {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} ∩
      {ω | (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)} := by
    refine ⟨?_, ?_⟩
    · show σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)
      rw [hσv]
      exact WithTop.coe_lt_coe.2 hN'
    · show (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)
      rw [hτv]
  have hcond : γ ω ((σ N ω).untopD 0 : ℝ≥0) ∈ H ∧ 0 < (min (t : WithTop ℝ≥0) (T n ω)).untopD 0 ∧
      (((min (t : WithTop ℝ≥0) (T n ω)).untopD 0 : ℝ≥0) : ℝ≥0∞) <
        firstContactTime (fun u => (α ω u : OnePoint ℂ))
          ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ N ω).untopD 0 : ℝ≥0)) := by
    rw [hσv, hτv, WithTop.untopD_coe, WithTop.untopD_coe]
    exact ⟨hγH, ht0, hfc⟩
  have h := hall N n hmem hcond w hw hpair
  rwa [hσv, hτv, WithTop.untopD_coe, WithTop.untopD_coe] at h

end InteractingSLE.Theorem14.GW2Kb
