/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedAdaptUnion
import InteractingSLE.Spec.Sec5.CrossCondThetaMean

/-!
# Proposition 5.9, S2 on the glued space: the cobounded limit for an arbitrary recorded flow side

Packet PROVE-STAGED7 (PROVE-STAGED6 §5.2 item 2). The θ-template `Theta.ae_tendsto_union_sub_cfMean_coboundedT`
(the union mean minus the counterflow mean tends to `0` at infinity) with the flow hull `hullAt q (killedHistory …)`
replaced by an arbitrary recorded flow side `𝔄 ∘ Yf` (a local set of the centred field on `(Ω, P)`, relatively closed
in `ℍ` and bounded, whose lower union has no bounded component). The proof is the template's: reflect by
`z ↦ −1/z`, apply Proposition 3.8 for the union at the point `0` (the reflected flow side stays away from `0`
because it is bounded), and read the limit back at infinity. For Proposition 5.9's staged prefix use
`𝔄 := recHull s n`, `Yf := pastMap … (n + 1)` (`exists_flowSide_schedule`, `not_isBounded_lowerUnion_recHull`,
`isHPHull_recHull`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull fwdMap)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedCand

open WangWu hiding ratPt exists_ratPt_dist_lt continuousAt_negInv
open WangWu.ImgWord LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q WholeField Word49 Sec7.StripSysField
open GlueImg Theta
open LocalSets (IsLocalSetMean lowerUnion)

section Inf

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}
  {γ : Type*} [mγ : MeasurableSpace γ] {Yf : Ω → γ} {𝔄 : γ → Set ℂ}

/-- **The cobounded limit on the θ-glued space for an arbitrary recorded flow side** (θ-template
`Theta.ae_tendsto_union_sub_cfMean_coboundedT` with the flow hull replaced by `𝔄 ∘ Yf`): almost surely on the glued
space, every harmonic representative `w` of the union mean minus every harmonic representative `wG` of the
counterflow mean tends to `0` at infinity in `ℍ ∖ (𝔄 (Yf p.1) ∪ G_t)`. -/
theorem ae_tendsto_union_sub_cfMean_coboundedT_flowSide
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hYf : Measurable Yf) (h𝔄 : Measurable[mγ, hittingSigma] 𝔄)
    (hrelA : ∀ y, 𝔄 y ⊆ H ∧ IsOpen (H \ 𝔄 y)) (hbdA : ∀ y, Bornology.IsBounded (𝔄 y))
    (hAl : IsLocalSet (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P)
    (t : ℝ≥0) {g gG : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => 𝔄 (Yf p.1) ∪ cfHullQ t p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) g)
    (hgG : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) gG) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)), ∀ w wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w (H \ (𝔄 (Yf p.1) ∪ cfHullQ t p.2)) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ (𝔄 (Yf p.1) ∪ cfHullQ t p.2) → g p φ = ∫ z, w z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ cfHullQ t p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ t p.2 → gG p φ = ∫ z, wG z * φ z) →
      Tendsto (fun z => w z - wG z)
        (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (𝔄 (Yf p.1) ∪ cfHullQ t p.2))) (𝓝 0) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  set Aω : Ω → Set ℂ := fun ω => 𝔄 (Yf ω) with hAωdef
  have hAm : Measurable[mΩ, hittingSigma] Aω := h𝔄.comp hYf
  have hreg₂ := ae_cfRegT hκ hθb hC hcf hlaw
  have hAg := IsLocalSet.glue_fst hXm k (T := cenTT κ θ u₀) hAl
  have hGg := IsLocalSet.glue_snd hXm k (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)
    (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw hk
    (measurable_cenTT κ θ u₀) (measurable_cfHullQ t) MeasurableSet.univ (fun y _ => cfHullQ_relClosed t y)
    (Eventually.of_forall fun _ => mem_univ _) (isLocalSet_cfHullQ_cenTT hcf hreg₂ hu₀.1 t)
  -- the glued field and its reflection are zero-boundary GFFs
  have hF0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
    have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 0 0 =>
      cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) μ :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hXm) hF0
  have hFR := isZeroBoundaryGFF_reflectField hF
  -- the reflected hulls: `R(A)` and `R(G) = K′_t`
  have hA₁ : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 => negInv '' Aω p.1 := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact measurable_image_negInv.comp (hAm.comp measurable_fst)
  have hA₂ : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 => hullAt t p.2 := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact (measurable_hullAt t).comp measurable_snd
  have hAωR : Measurable[mΩ, hittingSigma] fun ω => negInv '' Aω ω := by
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    exact measurable_image_negInv.comp hAm
  have hci := condIndepEv_glue_sets (P := P) hXm k (T := fun f => reflectField (cenTT κ θ u₀ f))
    (measurable_reflectField.comp (measurable_cenTT κ θ u₀)) (T' := fun f => cenTT' κ θ u₀ (reflectField f))
    ((measurable_cenTT' κ θ u₀).comp measurable_reflectField)
    (fun f => by
      show cenTT' κ θ u₀ (reflectField (reflectField (cenTT κ θ u₀ f))) = f
      rw [reflectField_reflectField, cenTT'_cenTT]) hAωR (measurable_hullAt t)
  have hGG : (fun p : Ω × HistorySpace 0 0 => negInv '' cfHullQ t p.2) = fun p => hullAt t p.2 :=
    funext fun p => image_negInv_image_negInv _
  have h₁ := WangWu.IsLocalSet.reflect hAg
  have h₂ := WangWu.IsLocalSet.reflect hGg
  rw [hGG] at h₂
  have hunb : ∀ᵐ p ∂μ, ∀ z ∈ LocalSets.lowerUnion (hullAt t p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion (hullAt t p.2)) z) :=
    Eventually.of_forall fun p => not_isBounded_lowerUnion_of_isHPHull (isHPHull_hullAt _ _)
  have hrel : ∀ p : Ω × HistorySpace 0 0, (Aω p.1 ∪ cfHullQ t p.2) ⊆ H ∧ IsOpen (H \ (Aω p.1 ∪ cfHullQ t p.2)) := by
    intro p
    obtain ⟨h1, h1o⟩ := hrelA (Yf p.1)
    obtain ⟨h2, h2o⟩ := cfHullQ_relClosed t p.2
    refine ⟨union_subset h1 h2, ?_⟩
    rw [← Set.sdiff_inter_sdiff]; exact h1o.inter h2o
  have hg' := WangWu.IsLocalSetMean.reflect hrel hg
  have hUU : (fun p : Ω × HistorySpace 0 0 => negInv '' (Aω p.1 ∪ cfHullQ t p.2)) =
      fun p => negInv '' Aω p.1 ∪ hullAt t p.2 := by
    funext p; rw [image_union, cfHullQ, image_negInv_image_negInv]
  have hg'' : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => negInv '' Aω p.1 ∪ hullAt t p.2)
      (fun p => reflectField (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))) μ (fun p => reflectField (g p)) := by
    rw [← hUU]; exact hg'
  have hgG' : IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => hullAt t p.2)
      (fun p => reflectField (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))) μ (fun p => reflectField (gG p)) := by
    have := WangWu.IsLocalSetMean.reflect (A := fun p : Ω × HistorySpace 0 0 => cfHullQ t p.2)
      (h := fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) (g := gG) (fun p => cfHullQ_relClosed t p.2) hgG
    rw [hGG] at this
    exact this
  have h38 := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hFR hA₁ hA₂ hci h₁ h₂ hunb hg'' hgG'
  filter_upwards [h38] with p ⟨u, hu, hrep, hlim⟩
  intro w wG hw hrepw hwG hrepwG
  set C := H \ (Aω p.1 ∪ cfHullQ t p.2) with hCdef
  have hCo : IsOpen C := (hrel p).2
  have hCH : C ⊆ H := sdiff_subset
  have hCG : C ⊆ H \ cfHullQ t p.2 := fun z hz => ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩
  have hRC : H \ (negInv '' Aω p.1 ∪ hullAt t p.2) = negInv '' C := by
    rw [← image_negInv_image_negInv (hullAt t p.2), ← image_union, H_diff_image_negInv]
    rfl
  -- `u = −w ∘ R + w_G ∘ R` on `R(C)`
  have hRCo : IsOpen (negInv '' C) := isOpen_image_negInv hCo hCH
  have hRCH : negInv '' C ⊆ H := image_negInv_subset_H hCH
  have hw' := harmonicOnNhd_comp_negInv hCo hCH hw
  have hwG' := harmonicOnNhd_comp_negInv hCo hCH (fun z hz => hwG z (hCG hz))
  have hv : InnerProductSpace.HarmonicOnNhd (fun z => -w (negInv z) + wG (negInv z)) (negInv '' C) :=
    fun z hz => (hw' z hz).neg.add (hwG' z hz)
  have hcont : ∀ {v : ℂ → ℝ} {U : Set ℂ}, InnerProductSpace.HarmonicOnNhd v U → ContinuousOn v U :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hu' : InnerProductSpace.HarmonicOnNhd u (negInv '' C) := by rw [← hRC]; exact hu
  have heq : EqOn u (fun z => -w (negInv z) + wG (negInv z)) (negInv '' C) := by
    refine Sec6.eqOn_of_integral_mul_eq hRCo hRCH hu' hv fun φ hφ => ?_
    have hφ' : tsupport φ ⊆ H \ (negInv '' Aω p.1 ∪ hullAt t p.2) := by rw [hRC]; exact hφ
    have i1 := LocalSets.integrable_mul_test hRCo (hcont hw').neg φ hφ
    have i2 := LocalSets.integrable_mul_test hRCo (hcont hwG') φ hφ
    have e1 := reflectField_rep hrepw φ hφ
    have e2 := reflectField_rep (U := H \ cfHullQ t p.2) hrepwG φ (hφ.trans (image_mono hCG))
    rw [← hrep φ hφ', e1, e2]
    have i1' : Integrable fun z => -w (negInv z) * φ z := i1
    have i2' : Integrable fun z => -wG (negInv z) * φ z := by
      refine i2.neg.congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.neg_apply, Function.comp_apply, neg_mul]
    rw [← integral_sub i1' i2']
    congr 1; funext z; ring
  -- the limit at `0` of the chart `R`
  obtain ⟨M, hM⟩ := (hbdA (Yf p.1)).subset_closedBall 0
  have hM0 : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hloc : ∃ r > 0, negInv '' Aω p.1 ∩ ball 0 r ⊆ hullAt t p.2 := by
    refine ⟨(max M 1)⁻¹, inv_pos.2 hM0, ?_⟩
    rintro _ ⟨⟨a, ha, rfl⟩, hb⟩
    exfalso
    have ha' : ‖a‖ ≤ max M 1 := by
      have := hM ha
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have ha0 : a ≠ 0 := ne_zero_of_mem_H ((hrelA (Yf p.1)).1 ha)
    rw [mem_ball, dist_zero_right, norm_negInv] at hb
    have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
    have := (inv_lt_inv₀ hapos hM0).1 hb
    linarith
  have h0 := hlim 0 (Or.inr (by simp)) hloc
  rw [hRC] at h0
  refine tendsto_cobounded_of_negInv (u := fun z => -u z) (fun z hz => ?_) ?_
  · have := heq (mem_image_of_mem negInv hz)
    simp only [WangWu.negInv_negInv] at this
    rw [this]; ring
  · simpa using h0.neg

end Inf

end InteractingSLE.Sec5.CrossCond.StagedCand
