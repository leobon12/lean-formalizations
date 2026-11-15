/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5SameHeight
import InteractingSLE.Spec.Supplement.SB2FinCompP38

/-! # GW4: ambient heights through the incident component

The R.5 ambient hull mean is identified by the committed coupling theorem.
The component form of Proposition 3.8 then compares a union mean with that
mean along every incident component free of the other local set. This also
handles accesses over a contact point; no whole-ball separation is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Sec7.Aux119Heights Sec7.R5Same SB.FinRel

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The actual ambient coupling identifies a union mean at every prime end
approached through components missing the other local set. -/
theorem ae_tendsto_ambientMean_freeNear
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
      (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (s : ℝ≥0)
    (hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω)
    {K : Ω → Set ℂ} (hKm : Measurable[mΩ, hittingSigma] K)
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) s)
    {E : Ω → Set ℂ} (hEm : Measurable[mΩ, hittingSigma] E)
    (hEd : MeasurableSpace.comap E hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P)
    (hEl : IsLocalSet E (centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => E ω ∪ K ω) (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ GE : ℂ → ℝ, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω)
          (fun j => VR j s ω - W s ω))
        (forceJumpSet (fun i => VL i s ω - W s ω) (fun j => VR j s ω - W s ω)) GE →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (E ω ∪ K ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (E ω ∪ K ω) →
        g ω φ = ∫ z, v z * φ z) →
      ∀ z₀ ∈ K ω ∪ {z : ℂ | z.im = 0}, ∀ r > 0,
        Tendsto (fun z => v z + u₀ z + chiC κ *
          (logDerivFwd (fun t : ℝ => W t.toNNReal ω) s z).im -
            GE (fwdMap (fun t : ℝ => W t.toNNReal ω) s z))
          (𝓝[freeNear (E ω) (K ω) z₀ r] z₀) (𝓝 0) := by
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have hKl := isLocalSet_hull hC hu₀ hX s hsζ hKeq
  obtain ⟨g₂, hg₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hKm hKl
  have hci : LQGMetric.CondIndepEv
      (MeasurableSpace.comap (centredField h u₀) inferInstance)
      (MeasurableSpace.comap E hittingSigma) (MeasurableSpace.comap K hittingSigma) P :=
    Sec6.condIndepEv_of_le_aeSigma hh0.measurable.comap_le hKm.comap_le hEd
  have hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z) := by
    filter_upwards [hKeq, hC.1.2.2.2.2, hsζ] with ω hKω hp hlt
    rw [hKω]
    exact Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull
      (Sec5.CrossRestart.isHPHull_fwdHull_rpath hp.2.2.2.1 hlt)
  filter_upwards [ae_tendsto_sub_of_union_comp hh0 hEm hKm hci hEl hKl hunb hg hg₂,
    ae_eqOn_hullMean hC hκ hu₀ hX s hsζ hKm hKeq hg₂,
    hg₂.2.1, hKl.2.1, hEl.2.1]
    with ω ⟨u, hu, hurep, hulim⟩ hHM hg₂ω ⟨_, hKo⟩ ⟨_, hEo⟩
      GE hGE v hv hrep z₀ hz₀ r hr
  obtain ⟨w₂, hw₂, hrep₂⟩ := hg₂ω
  have hUeq : H \ (E ω ∪ K ω) = (H \ E ω) ∩ (H \ K ω) := by
    ext z
    simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
    tauto
  have hoU : IsOpen (H \ (E ω ∪ K ω)) := hUeq ▸ hEo.inter hKo
  have hUK : H \ (E ω ∪ K ω) ⊆ H \ K ω := sdiff_subset_sdiff_right subset_union_right
  have hcont : ∀ {U : Set ℂ} {w : ℂ → ℝ}, InnerProductSpace.HarmonicOnNhd w U →
      ContinuousOn w U := fun hw z hz => (hw z hz).1.continuousAt.continuousWithinAt
  have huv : EqOn u (fun z => v z - w₂ z) (H \ (E ω ∪ K ω)) := by
    refine Sec6.eqOn_of_integral_mul_eq hoU sdiff_subset hu
      (hv.sub fun z hz => hw₂ z (hUK hz)) fun φ hφ => ?_
    rw [← hurep φ hφ, hrep φ hφ, hrep₂ φ (hφ.trans hUK),
      ← integral_sub (integrable_mul_test hoU (hcont hv) φ hφ)
        (integrable_mul_test hoU ((hcont hw₂).mono hUK) φ hφ)]
    congr 1
    funext z
    ring
  have hE := hHM GE hGE w₂ hw₂ hrep₂
  refine (hulim z₀ hz₀ r hr).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hzU := freeNear_subset hz
  have h1 := huv hzU
  have h2 := hE (hUK hzU)
  simp only at h1 h2 ⊢
  rw [h1, ← h2]
  ring

/-- At a real non-jump ambient image, the incident-component comparison
gives the actual ambient finite-word height in its inherited lift. -/
theorem ae_tendsto_ambientWord_freeNear
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
      (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (s : ℝ≥0)
    (hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω)
    {K : Ω → Set ℂ} (hKm : Measurable[mΩ, hittingSigma] K)
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) s)
    {E : Ω → Set ℂ} (hEm : Measurable[mΩ, hittingSigma] E)
    (hEd : MeasurableSpace.comap E hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P)
    (hEl : IsLocalSet E (centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => E ω ∪ K ω) (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ K ω ∪ {z : ℂ | z.im = 0},
      ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun i => VL i s ω - W s ω) (fun j => VR j s ω - W s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) →
      (∃ r > 0, ∀ᶠ y in 𝓝[H] ξ, F y ∈ freeNear (E ω) (K ω) z₀ r) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W t.toNNReal ω) s (F y))
        (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ (E ω ∪ K ω)) (F y) + u₀ (F y) +
        chiC κ * (logDerivFwd (fun t : ℝ => W t.toNNReal ω) s (F y)).im)
        (𝓝[H] ξ) (𝓝 (forceBoundaryData κ ρL ρR
          (fun i => VL i s ω - W s ω) (fun j => VR j s ω - W s ω) x)) := by
  filter_upwards [ae_tendsto_ambientMean_freeNear hC hκ hu₀ hX s hsζ hKm hKeq hEm hEd hEl hg,
    hg.2.1, hC.1.2.2.2.2, hsζ, hKeq]
    with ω hcmp hgω hp hlt hKω z₀ hz₀ F ξ x hx hF ⟨r, hr, hFr⟩ hfF
  have hext := isBoundedHarmonicExtension_wordExt κ ρL ρR VL VR W s ω
  obtain ⟨hv, hrep⟩ := harmRep_spec hgω
  have hcmp' := hcmp _ hext _ hv hrep z₀ hz₀ r hr
  have hUK : H \ (E ω ∪ K ω) ⊆ H \ fwdHull (fun t : ℝ => W t.toNNReal ω) s :=
    hKω ▸ sdiff_subset_sdiff_right subset_union_right
  have hfF' : Tendsto (fun y => fwdMap (fun t : ℝ => W t.toNNReal ω) s (F y))
      (𝓝[H] ξ) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hfF, hFr.mono fun y hy =>
      Sec7.StripSideHeightProb.mapsTo_fwdMap_rpath hp.2.2.2.1 hlt (hUK (freeNear_subset hy))⟩
  exact tendsto_height_of_comparison hcmp' hF hFr hfF' (hext.2.2 x hx)

end InteractingSLE.Theorem14.GW4Fix
