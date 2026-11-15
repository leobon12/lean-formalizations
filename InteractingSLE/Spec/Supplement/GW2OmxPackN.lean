/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxPack
import InteractingSLE.Spec.Supplement.GW2OmxStop2

/-!
# GW2's open lines: the kernel means of the current stage for all caps at once

Packet PROVE-GW2-STAGEMEAN, R120 round. `GW2Omx.kernel_means` fixes the cap `N` of the stop `σ`; the localization
covers the live event by the events `{σ_N < N} ∩ {t ≤ T n}` over all `N` and `n`, so the counterflow's word `c'`, its
trace `γ`, the angle field `Xθ` and the announcing stops `T` must not depend on `N`.

* **`kernel_meansN`**: one unpacking of the launch datum gives the stops `σ N` of all caps (with the strict converse of
  `exists_stop_of_datum_ext2`), the zero-boundary GFF of the angle field centred by `u₀`, and the retained and union
  means at every `σ N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open Restart Exist Exist.StagedLaw WholeField LocalSets Sec7.PocketTraversal Supp8 Supp8.GB6 Supp8.GB6LineL
  Supp8.GB6LMean Supp8.Q3Chain RelSafeS GW2JointKernel GW2TipSystem GW2Fb GW2JDetR8
open Supp8.Q3Rel (invHull relLog)
open QuantumZipper (fwdMap logDerivFwd)
open QuantumZipper (fwdHull)

/-- **The retained (time-`0`) kernel mean with marked locality** for marks `𝓝` (the conclusion of
`GW2Stm.exists_retained_gw2_stop` with `𝓝 = F_σ`). -/
def RetMeanLocAt {Ω : Type u} [mΩ : MeasurableSpace Ω] (κ θ : ℝ) (P : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (c' : BoundaryWord) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (σ : Ω → WithTop ℝ≥0) (u₀ : ℂ → ℝ)
    (𝓝 : {m : MeasurableSpace Ω // m ≤ mΩ}) : Prop :=
  ∃ A : Ω → Set ℂ, Measurable[𝓝.1, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
    (∀ᵐ ω ∂P, A ω = invHull (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
    WholeField.IsHistoryAvoidanceLocal 𝓝.1 A (centredField X u₀) P ∧
    𝓝.1 ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
    ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (centredField X u₀) P g₁ →
      ∀ᵐ ω ∂P, ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
          (cfData κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps)
          (cfJumps (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + (u₀ z - θ * chiC κ))
            (fun z => G₀ (relMap (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z) -
              chiC κ * (relLog (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z).im)
            (H \ A ω)

/-- **The kernel means of the current stage for every cap `N`** (`kernel_means` with the stops `σ N` of all caps
from one unpacking, the zero-boundary GFF of the angle field and the strict converse of the stops). -/
theorem kernel_meansN (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hG : IsGFFWithBoundaryData μ X b J) {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ μ X Wk ζk) {W' : ℝ≥0 → Ω → ℝ}
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
    ∃ (σ : ℕ → Ω → WithTop ℝ≥0) (Xθ : Ω → DistOn upperHalfPlaneOpens) (T : ℕ → Ω → ℝ≥0) (c' : BoundaryWord)
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
  obtain ⟨h', h₁, c', 𝓕', VL', VR', B', γ, hX', hT, htr', hC', hcomp, hNR⟩ :=
    GW2Olm.counterflow_pack h13 hκ hκ4 hb hG hcf (hd.mono fun _ h => h.1)
  have hst := fun N : ℕ => exists_stop_of_datum_ext2 h13 hκ μ hcf hX' hW' hpb hd s (N : ℝ≥0)
  choose σ hσ hσt hσN hσeq hσconv hσlt using hst
  obtain ⟨Xθ, 𝓕, VL, VR, B, hX, T, htr, hC, hTa⟩ := GW2Olm.flowLine_pack hκ hfl hseed
  refine ⟨σ, Xθ, T, c', γ, htr, isZeroBoundaryGFF_centredField hC hu₀, hTa.2.2.2, ae_all_iff.2 hTa.2.2.1, hcomp,
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

end InteractingSLE.Theorem14.GW2Omx
