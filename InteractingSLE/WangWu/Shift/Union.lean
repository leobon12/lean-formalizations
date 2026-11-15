/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Shift.Bdry
import InteractingSLE.WangWu.Shift.Rev
import InteractingSLE.WangWu.ReverseContactBdryGlue

/-!
# The height-shifted two-slit law, part 4: the union of the two slits and its mean

Packet PROVE-WW-B26 (PROVE-WW-B11/B13/B14's `isLocalSet_twoSlit_glue`, `ae_union_mean_glue(_of_disjoint)` and
`ae_union_mean_eq_chartMean_glue` with the height shift). Setting (`ImageWordFiltShiftStatement`): the forward
coupling `hC` of `(r_L; r_R)` with the field `h`, the glued field `X` with `h = X + δλ`, a reverse coupling `hC₂` of
`(r_R − δ; r_L + δ)` whose reflected field has the law of `X`, the glued space `P ⊗ k(X)`. The centred field
`h − u₀ = X − (u₀ − δλ)` is shared (`Shift.centredField_shift`):

* **`isLocalSet_twoSlit_glue_shift`**: `α(0, t] ∪ R(β(0, s])` is a local set of the centred field on `P ⊗ k(X)`;
* `ae_union_mean_glue_shift`, `ae_union_mean_glue_of_disjoint_shift`: its mean `w` has boundary values `meanAt^α − u₀`
  at the forward slit and `revMean (r_L + δ) (r_R − δ) (u₀ − δλ)` at the reverse slit;
* **`ae_union_mean_eq_chartMean_glue_shift`**: before contact, `w + u₀ = chartMeanW ![r_L, −r_L − δ] ![r_R, −r_R + δ]
  ∘ f'_T ∘ Ψ`: the uncentred union mean is, in `Ψ`-coordinates, the explicit `SLE₄(r_L, −r_L − δ; r_R, −r_R + δ)` mean
  of the image slit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open LQGMetric (DistOn TestOn)
open LocalSets (IsLocalSetMean germSigma)
open LawUnique
open SupercriticalConformalCovariance.GM24 (smoothDist)
open SupercriticalConformalCovariance (IsConformalBijection)
open MartChar.RealFlow
open Sec4 (regPath posLProc posRProc)

universe u

section Glue

variable {rL rR δ : ℝ}
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- **Step (S2) with the height shift: the two stopped slits are a local set of the shared centred field on
`P ⊗ k(X)`.** -/
theorem isLocalSet_twoSlit_glue_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) :
    IsLocalSet (fun p : Ω × HistorySpace 1 1 => histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k X hXm) := by
  set u₁ : ℂ → ℝ := fun z => u₀ z + -(δ * wwLambda) with hu₁def
  have hu₁ := Shift.isBoundedHarmonicExtension_shift (δ := δ) hu₀
  set D := smoothDist upperHalfPlaneOpens u₀ with hD
  set D₁ := smoothDist upperHalfPlaneOpens u₁ with hD₁
  have hDh : IsHarmonicDistOn D H := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  have hDh₁ : IsHarmonicDistOn D₁ H := WholeField.isHarmonicDistOn_smoothDist hu₁.1
  have hcf := Shift.centredField_shift hX hu₀.1
  obtain ⟨hXk, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hT : Measurable fun f : DistOn upperHalfPlaneOpens => f - D₁ := WholeField.measurable_sub_dist D₁
  have hT' : Measurable fun f : DistOn upperHalfPlaneOpens => f + D₁ := Coupling.measurable_add_distOnConst D₁
  -- the forward hull, on `Ω` and on the glued space
  have hA : IsLocalSet (fun ω => histHull t (killedHistory W VL VR ζ ω)) (fun ω => X ω - D₁) P := by
    have h1 := WholeField.IsLocalSet.sub_dist (isLocalSet_histHull_twoSeed hL hR hC ht) hDh
    have e : (fun ω => h ω - D) = fun ω => X ω - D₁ := hcf
    rwa [e] at h1
  have hAm : Measurable[mΩ, hittingSigma] fun ω => histHull t (killedHistory W VL VR ζ ω) :=
    (measurable_histHull t).comp (measurable_killedHistory hXk)
  have hAg := IsLocalSet.glue_fst hXm k (T := fun f => f - D₁) hA
  -- the reflected reverse hull, on `Ω₂` and on the glued space
  have hG₂ : IsLocalSet (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
      (fun ω => reflectField (h₂ ω) - D₁) P₂ :=
    WholeField.IsLocalSet.sub_dist (IsLocalSet.reflect (isLocalSet_histHull_twoSeed hR₁ hL₁ hC₂ hs)) hDh₁
  have hGm : Measurable[_, hittingSigma] fun y : HistorySpace 1 1 => negInv '' histHull s y :=
    measurable_image_negInv.comp (measurable_histHull s)
  have hGg := IsLocalSet.glue_snd hXm k (measurable_reflectField.comp hC₂.2.1)
    (measurable_killedHistory hX₂) hlaw hk hT hGm MeasurableSet.univ
    (fun y _ => image_negInv_relClosed (histHull_relClosed s y)) (Eventually.of_forall fun _ => mem_univ _) hG₂
  have hZ₁ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => X ω - D₁) P :=
    Shift.isZeroBoundaryGFF_centredField_shift hX hu₀.1 (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have hU := IsLocalSet.glue_union hXm k hT hT' (fun f => sub_add_cancel f D₁) hZ₁ hAm hGm hAg hGg
  have e : (fun p : Ω × HistorySpace 1 1 => WholeField.centredField h u₀ p.1) = fun p => X p.1 - D₁ :=
    funext fun p => congrFun hcf p.1
  rw [e]
  exact hU

/-- **Step (S3a) with the height shift**: the union mean of the two stopped slits on `P ⊗ k(X)`, with its boundary
behaviour against the forward mean (word `(r_L; r_R)`, field `h`) and the reverse mean (word `(r_R − δ; r_L + δ)`,
field `X`, centred by `u₀ − δλ`). -/
theorem ae_union_mean_glue_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) {g : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k X hXm) g) :
    ∀ᵐ p ∂(glueMeasure P k X hXm),
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w
          (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) →
            g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ histHull t (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, negInv '' histHull s p.2 ∩ ball z₀ r ⊆ histHull t (killedHistory W VL VR ζ p.1)) →
          Tendsto (fun z => w z - (meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1)
              (fun i => (VL i · p.1)) (fun i => (VR i · p.1)) (Real.toNNReal t) z - u₀ z))
            (𝓝[H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ negInv '' histHull s p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, histHull t (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ negInv '' histHull s p.2) →
          Tendsto (fun z => w z - revMean (rL + δ) (rR - δ) (fun z => u₀ z + -(δ * wwLambda)) s p.2 z)
            (𝓝[H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)] z₀) (𝓝 0)) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set u₁ : ℂ → ℝ := fun z => u₀ z + -(δ * wwLambda) with hu₁def
  have hu₁ := Shift.isBoundedHarmonicExtension_shift (δ := δ) hu₀
  set D := smoothDist upperHalfPlaneOpens u₀ with hD
  set D₁ := smoothDist upperHalfPlaneOpens u₁ with hD₁
  have hDh : IsHarmonicDistOn D H := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  have hDh₁ : IsHarmonicDistOn D₁ H := WholeField.isHarmonicDistOn_smoothDist hu₁.1
  have hcf := Shift.centredField_shift hX hu₀.1
  obtain ⟨hXk, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hT : Measurable fun f : DistOn upperHalfPlaneOpens => f - D₁ := WholeField.measurable_sub_dist D₁
  have hT' : Measurable fun f : DistOn upperHalfPlaneOpens => f + D₁ := Coupling.measurable_add_distOnConst D₁
  have hZ₁ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField X u₁) P :=
    Shift.isZeroBoundaryGFF_centredField_shift hX hu₀.1 (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have e : (fun p : Ω × HistorySpace 1 1 => WholeField.centredField h u₀ p.1) =
      fun p => WholeField.centredField X u₁ p.1 := funext fun p => congrFun hcf p.1
  rw [e] at hg
  -- the two slits are local on the glued space
  have hA : IsLocalSet (fun ω => histHull t (killedHistory W VL VR ζ ω)) (fun ω => X ω - D₁) P := by
    have h1 := WholeField.IsLocalSet.sub_dist (isLocalSet_histHull_twoSeed hL hR hC ht) hDh
    have e' : (fun ω => h ω - D) = fun ω => X ω - D₁ := hcf
    rwa [e'] at h1
  have hAm : Measurable[mΩ, hittingSigma] fun ω => histHull t (killedHistory W VL VR ζ ω) :=
    (measurable_histHull t).comp (measurable_killedHistory hXk)
  have hAg := IsLocalSet.glue_fst hXm k (T := fun f => f - D₁) hA
  have hG₂ : IsLocalSet (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
      (fun ω => reflectField (h₂ ω) - D₁) P₂ :=
    WholeField.IsLocalSet.sub_dist (IsLocalSet.reflect (isLocalSet_histHull_twoSeed hR₁ hL₁ hC₂ hs)) hDh₁
  have hGm : Measurable[_, hittingSigma] fun y : HistorySpace 1 1 => negInv '' histHull s y :=
    measurable_image_negInv.comp (measurable_histHull s)
  have hGg := IsLocalSet.glue_snd hXm k (measurable_reflectField.comp hC₂.2.1)
    (measurable_killedHistory hX₂) hlaw hk hT hGm MeasurableSet.univ
    (fun y _ => image_negInv_relClosed (histHull_relClosed s y)) (Eventually.of_forall fun _ => mem_univ _) hG₂
  -- the two slit means
  obtain ⟨gA₀, hgA₀, hidA₀⟩ := exists_isLocalSetMean_histHull_twoSeed hL hR hC hu₀ ht
  rw [hcf] at hgA₀
  have hgA : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 => histHull t (killedHistory W VL VR ζ p.1))
      (fun p => WholeField.centredField X u₁ p.1) (glueMeasure P k X hXm) (fun p => gA₀ p.1) :=
    IsLocalSetMean.comp measurable_fst (glueMeasure_fst (μ := P) k hXm) hAm
      (WholeField.measurable_centredField hXm u₁) hgA₀
  have hidA := ae_glue_fst k hXm hidA₀
  obtain ⟨gG₀, -, hgG, -⟩ := exists_isLocalSetMean_revSlit_canonX hL₁ hR₁ hXm hC₂ hlaw k hk hu₁ hZ₁ hs
  obtain ⟨hreg, hidG⟩ := ae_revSlitMean_glueX hL₁ hR₁ hXm hC₂ hlaw k hk hu₁ hZ₁ hs hgG
  -- the unbounded-components conditions
  have hunbA : ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ z ∈ LocalSets.lowerUnion (histHull t (killedHistory W VL VR ζ p.1)),
      ¬ Bornology.IsBounded (connectedComponentIn
        (LocalSets.lowerUnion (histHull t (killedHistory W VL VR ζ p.1))) z) :=
    ae_glue_fst k hXm (by
      filter_upwards [ae_mem_goodHist_twoSeed hL hR hC.1 t] with ω hω
      exact LocalSets.not_isBounded_of_isPreconnected_union_real (isPreconnected_histHull_union_real ht hω))
  -- the union boundary lemma (PROVE-WW-B12)
  have hU := ae_union_boundary_glue (P := P) hXm k hT hT' (fun f => sub_add_cancel f D₁) hZ₁ hAm hGm hAg hGg
    hunbA (ae_unb_revSlit_glueX hL₁ hR₁ hXm hC₂ hlaw k hk hs) hg hgA hgG
  -- the forward mean is harmonic off the forward slit
  have hseed := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1
  have hfwd : ∀ᵐ p ∂(glueMeasure P k X hXm), InnerProductSpace.HarmonicOnNhd
      (fun z => meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1) (fun i => (VL i · p.1))
        (fun i => (VR i · p.1)) (Real.toNNReal t) z - u₀ z) (H \ histHull t (killedHistory W VL VR ζ p.1)) := by
    refine ae_glue_fst (μ := P) k hXm (Q := fun ω => InnerProductSpace.HarmonicOnNhd
      (fun z => meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · ω) (fun i => (VL i · ω))
        (fun i => (VR i · ω)) (Real.toNNReal t) z - u₀ z) (H \ histHull t (killedHistory W VL VR ζ ω))) ?_
    filter_upwards [hseed, hC.1.2.2.2.2, ae_histHull_eq_fwdHull hL hR hC.1 ht] with ω hω hp hH
    rw [hH]
    have hlt : ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hω.1]; exact ENNReal.coe_lt_top
    exact (harmonicOnNhd_meanAt_of_lt hp hlt).sub fun z hz => hu₀.1 z hz.1
  -- the forward explicit mean, recentred
  have hidA' : ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ φ : TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ H \ histHull t (killedHistory W VL VR ζ p.1) →
      gA₀ p.1 φ = ∫ z, (meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1) (fun i => (VL i · p.1))
        (fun i => (VR i · p.1)) (Real.toNNReal t) z - u₀ z) * φ z := hidA
  filter_upwards [hU, hidA', hidG, hreg, hfwd] with p hUp hAp hGp hregp hfwdp
  have hwG : InnerProductSpace.HarmonicOnNhd (revMean (rL + δ) (rR - δ) u₁ s p.2)
      (H \ negInv '' histHull s p.2) := by
    intro z hz
    refine harmonicOnNhd_revMean (rL + δ) (rR - δ) hu₁.1 s p.2 z ⟨hz.1, fun hzF => hz.2 ?_⟩
    obtain ⟨w, hw, hwz⟩ := hzF
    exact ⟨w, hregp (fwdHull_subset_regHull s p.2 hw), hwz⟩
  exact hUp _ _ hfwdp hAp hwG hGp

/-- **Before contact** (`A ∩ G = ∅`): almost surely the union mean has a harmonic representative `w` with
`w − (meanAt^α_t − u₀) → 0` at **every** point of `A ∪ ℝ`, and `w − revMean → 0` at every point of `G` and every
nonzero real point (`G` is closed in `ℂ` and misses `ℝ`; the closure of `A` adds only `0`). -/
theorem ae_union_mean_glue_of_disjoint_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) {g : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k X hXm) g) :
    ∀ᵐ p ∂(glueMeasure P k X hXm),
      Disjoint (histHull t (killedHistory W VL VR ζ p.1)) (negInv '' histHull s p.2) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w
          (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) →
            g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ histHull t (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          Tendsto (fun z => w z - (meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1)
              (fun i => (VL i · p.1)) (fun i => (VR i · p.1)) (Real.toNNReal t) z - u₀ z))
            (𝓝[H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ negInv '' histHull s p.2 ∪ ({z : ℂ | z.im = 0} \ {0}),
          Tendsto (fun z => w z - revMean (rL + δ) (rR - δ) (fun z => u₀ z + -(δ * wwLambda)) s p.2 z)
            (𝓝[H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)] z₀) (𝓝 0)) := by
  filter_upwards [ae_union_mean_glue_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs hg,
    ae_glue_fst (μ := P) k hXm (Q := fun ω => killedHistory W VL VR ζ ω ∈ GoodHist t)
      (ae_mem_goodHist_twoSeed hL hR hC.1 t), ae_goodHist_snd_glueX hL₁ hR₁ hXm hC₂ hlaw k hk s]
    with p hp hA hG hdis
  obtain ⟨w, hw, hrep, hlimA, hlimG⟩ := hp
  set A := histHull t (killedHistory W VL VR ζ p.1) with hAdef
  set G := negInv '' histHull s p.2 with hGdef
  have hGc : IsClosed G := isClosed_image_negInv_histHull hs hG
  have hGH : G ⊆ H := (image_negInv_relClosed (histHull_relClosed s p.2)).1
  have hAcl : closure A ⊆ insert 0 A := closure_histHull_subset ht hA
  refine ⟨w, hw, hrep, fun z₀ hz₀ => hlimA z₀ hz₀ ?_, fun z₀ hz₀ => hlimG z₀ ?_ ?_⟩
  · -- a ball around `z₀` misses `G`
    have hz₀G : z₀ ∉ G := by
      rcases hz₀ with hz | hz
      · exact Set.disjoint_left.1 hdis hz
      · intro hzG
        have : 0 < z₀.im := hGH hzG
        rw [show z₀.im = 0 from hz] at this
        exact lt_irrefl _ this
    obtain ⟨r, hr, hrG⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl z₀ hz₀G
    exact ⟨r, hr, fun z hz => absurd hz.1 (hrG hz.2)⟩
  · rcases hz₀ with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz.1
  · -- a ball around `z₀` misses `A`
    have hz₀A : z₀ ∉ closure A := by
      intro hzc
      rcases hAcl hzc with h0 | hzA
      · rcases hz₀ with hz | hz
        · have : 0 < z₀.im := hGH hz
          rw [h0] at this
          simp at this
        · exact hz.2 h0
      · rcases hz₀ with hz | hz
        · exact Set.disjoint_left.1 hdis hzA hz
        · have : 0 < z₀.im := (histHull_relClosed t _).1 hzA
          rw [show z₀.im = 0 from hz.1] at this
          exact lt_irrefl _ this
    obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z₀ hz₀A
    exact ⟨r, hr, fun z hz => absurd (subset_closure hz.1) (hrA hz.2)⟩

/-- **Step (S3) of the contact step, completed before contact.** On the glued space, almost surely on
`{A ∩ G = ∅}` (`A = α((0, t])`, `G = R(β((0, s]))`), the union mean of the two stopped slits has a harmonic
representative `w` on `C = ℍ \ (A ∪ G)` and the image chain `W'` of `Ψ(A)` (`Ψ = revChart` of the reverse frozen
driver) exists, with `w + u₀ = chartMean ∘ f'_T ∘ Ψ` on `C`: the uncentred union mean is, in `Ψ`-coordinates, the
explicit `SLE₄(r_L, −r_L; r_R, −r_R)` mean of the image slit with forces at the images of `0∓` and of `Ψ(∞∓)`. -/
theorem ae_union_mean_eq_chartMean_glue_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) {g : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k X hXm) g) :
    ∀ᵐ p ∂(glueMeasure P k X hXm),
      Disjoint (histHull t (killedHistory W VL VR ζ p.1)) (negInv '' histHull s p.2) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w
          (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) →
            g p φ = ∫ z, w z * φ z) ∧
        ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
          IsProperArc η' ∧
          fwdHull W' T = revChart (Ito.rpath (frzDrive s p.2)) s '' histHull t (killedHistory W VL VR ζ p.1) ∧
          ∀ z ∈ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2),
            w z + u₀ z = chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T (frzVL s p.2) (frzVR s p.2)
              (fwdMap W' T (revChart (Ito.rpath (frzDrive s p.2)) s z)) := by
  obtain ⟨hXk, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh := hXm
  -- Corollary 4.8 through a half-plane chart, on the glued space
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 1 1 =>
      WholeField.centredField h u₀ p.1) (glueMeasure P k X hh) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => WholeField.centredField h u₀ ω) (f := Prod.fst)
      measurable_fst (glueMeasure_fst (μ := P) k hh) (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have hloc := isLocalSet_twoSlit_glue_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 => histHull t (killedHistory W VL VR ζ p.1) :=
    (measurable_histHull t).comp ((measurable_killedHistory hXk).comp measurable_fst)
  have hGm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2 :=
    (measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd
  have hcor := ae_eqOn_of_condMean_halfPlaneChart hF
    (fun φ => Sec6.IsLocalSetMean.ae_eq_condExp_germSigma hF (LocalSets.measurable_union_hitting hAm hGm) hloc hg φ)
    (hloc.2.1.mono fun _ hp => hp.2)
  -- forward facts
  have hfwd : ∀ᵐ p ∂(glueMeasure P k X hh), Continuous (fun r => W r p.1) ∧ W 0 p.1 = 0 ∧
      IsLoewnerTrace (Ito.rpath (W · p.1)) (seedLine ζ W p.1) ∧ IsProperArc (seedLine ζ W p.1) ∧
      histHull t (killedHistory W VL VR ζ p.1) = fwdHull (Ito.rpath (W · p.1)) t ∧
      ∀ z, meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1) (fun i => (VL i · p.1))
        (fun i => (VR i · p.1)) (Real.toNNReal t) z = fwdSlitMean rL rR (Ito.rpath (W · p.1)) t z := by
    refine ae_glue_fst (μ := P) k hh (Q := fun ω => Continuous (fun r => W r ω) ∧ W 0 ω = 0 ∧
      IsLoewnerTrace (Ito.rpath (W · ω)) (seedLine ζ W ω) ∧ IsProperArc (seedLine ζ W ω) ∧
      histHull t (killedHistory W VL VR ζ ω) = fwdHull (Ito.rpath (W · ω)) t ∧
      ∀ z, meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · ω) (fun i => (VL i · ω))
        (fun i => (VR i · ω)) (Real.toNNReal t) z = fwdSlitMean rL rR (Ito.rpath (W · ω)) t z) ?_
    filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1,
      ae_histHull_eq_fwdHull hL hR hC.1 ht, hC.1.2.2.2.2] with ω hω hH hp
    obtain ⟨hζ, -, hLT, hP, -⟩ := hω
    have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
    have hTt : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht'
    have hWc : Continuous fun r => W r ω := by
      have h1 := hp.2.2.2.1
      rw [hζ] at h1
      exact continuousOn_univ.1 (h1.mono fun r _ => ENNReal.coe_lt_top)
    have hTζ : ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    refine ⟨hWc, hp.1, hLT, hP, ?_, fun z => ?_⟩
    · rw [hH, hTt]; rfl
    · have hvL := vL_eq_neg_rightImg hp hWc hTζ 0
      have hvR := vR_eq_rightImg hp hWc hTζ 0
      have hrT : Ito.rpath (W · ω) t = W (Real.toNNReal t) ω := rfl
      simp only [meanAt, fwdSlitMean, chartAL, chartAR, hTt]
      congr 1
      · funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [hvL, hrT]
        simp [LP.twoSeedXL, hTt]
      · funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [hvR, hrT]
        simp [LP.twoSeedXR, hTt]
  -- reverse facts
  have hrev : ∀ᵐ p ∂(glueMeasure P k X hh), p.2 ∈ BetaSet s :=
    ae_glue_snd (X₂ := fun ω => reflectField (h₂ ω)) (D₂ := killedHistory W₂ VL₂ VR₂ ζ₂) hh
      (measurable_reflectField.comp hC₂.2.1) (measurable_killedHistory hX₂) hlaw k hk
      (measurableSet_betaSet s) (ae_killedHistory_mem_betaSet hR₁ hL₁ hC₂.1 hs)
  filter_upwards [ae_union_mean_glue_of_disjoint_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs hg, hcor,
    hfwd, hrev, ae_goodHist_snd_glueX hL₁ hR₁ hXm hC₂ hlaw k hk s] with p hp hcorp hfp hrp hgp hdisj
  obtain ⟨w, hw, hrep, hlimA, hlimG⟩ := hp hdisj
  obtain ⟨hWc, hW0, hLT, hP, hAeq, hmeanA⟩ := hfp
  obtain ⟨hWβ, hWβ0, hβ, hβp, hGeq, hvL, hvR⟩ := trace_of_mem_betaSet hs hrp
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  set A := histHull t (killedHistory W VL VR ζ p.1) with hAdef
  set G := negInv '' histHull s p.2 with hGdef
  set Wα := Ito.rpath (W · p.1) with hWαdef
  set Wβ := Ito.rpath (frzDrive s p.2) with hWβdef
  have hGclosed : IsClosed (negInv '' fwdHull Wβ s) := by
    rw [← hGeq]; exact isClosed_image_negInv_histHull hs hgp
  have hdisj' : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s) := by rw [← hAeq, ← hGeq]; exact hdisj
  have hWαc : Continuous Wα := continuous_rpath hWc
  have hWα0 : Wα 0 = 0 := by simp [hWαdef, Ito.rpath, hW0]
  obtain ⟨W', hW', hW'0, T, hT, η', hη', hη'p, hK', htip⟩ :=
    exists_imageTrace hLT hP hWβ hWβ0 hs'.le hGclosed ht' hdisj'
  have hCeq : H \ (A ∪ G) = H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) := by rw [hAeq, hGdef, hGeq]
  -- the two boundary limits for `M = w + u₀`
  have hA' : ∀ z₀ ∈ fwdHull Wα t ∪ {z : ℂ | z.im = 0},
      Tendsto (fun z => (w z + u₀ z) - fwdSlitMean rL rR Wα t z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0) := by
    intro z₀ hz₀
    rw [← hCeq]
    have := hlimA z₀ (by rw [hAeq]; exact hz₀)
    refine this.congr fun z => ?_
    rw [hmeanA z]; ring
  have hG' : ∀ z₀ ∈ negInv '' fwdHull Wβ s ∪ ({z : ℂ | z.im = 0} \ {0}),
      Tendsto (fun z => (w z + u₀ z) + revSlitMean (rL + δ) (rR - δ) Wβ s (frzVL s p.2) (frzVR s p.2) z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 (δ * wwLambda)) := by
    intro z₀ hz₀
    rw [← hCeq]
    have := (hlimG z₀ (by rw [hGdef, hGeq]; exact hz₀)).add_const (δ * wwLambda)
    rw [zero_add] at this
    refine this.congr fun z => ?_
    rw [revMean_eq_revSlitMean _ hs]
    ring
  obtain ⟨E, hEfin, hE⟩ := exists_finite_tendsto_twoSlitChart_shift hLT hP hWαc hWα0 ht' hWβ hWβ0 hβ hβp hs' hGclosed
    hdisj' hW' hW'0 hη' hη'p hT hK' htip hvL hvR hA' hG'
  -- the chart of `C`
  have hΦ : IsConformalBijection (twoSlitChart Wβ s W' T) H (H \ (A ∪ G)) := by
    have h1 := isConformalBijection_comp_fwdMapInv (isConformalBijection_revChartInv hWβ hWβ0 hs'.le) hW' hW'0
      hT.le
    have hset : (H \ negInv '' fwdHull Wβ s) \ revChartInv Wβ s '' fwdHull W' T = H \ (A ∪ G) := by
      rw [hCeq, hK', image_image]
      have himg : (fun a => revChartInv Wβ s (revChart Wβ s a)) '' fwdHull Wα t = fwdHull Wα t := by
        refine (image_congr fun a ha => revChartInv_revChart hWβ hWβ0 hs'.le
          ⟨ha.1, fun h' => disjoint_left.1 hdisj' ha h'⟩).trans (image_id' _)
      rw [himg]
      ext z; simp only [Set.mem_sdiff, mem_union, not_or]; tauto
    rw [hset] at h1
    exact h1
  -- the candidate
  set v : ℂ → ℝ := fun z => chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T (frzVL s p.2) (frzVR s p.2)
    (fwdMap W' T (revChart Wβ s z)) - u₀ z with hvdef
  have hCH : ∀ z ∈ H \ (A ∪ G), z ∈ H \ negInv '' fwdHull Wβ s := fun z hz =>
    ⟨hz.1, fun h' => hz.2 (Or.inr (by rw [hGdef, hGeq]; exact h'))⟩
  have hCA : ∀ z ∈ H \ (A ∪ G), revChart Wβ s z ∈ H \ fwdHull W' T := fun z hz => by
    refine ⟨revChart_mem_H hWβ hs'.le (hCH z hz), fun hK => ?_⟩
    rw [hK'] at hK
    obtain ⟨a, ha, e⟩ := hK
    have := injOn_revChart hWβ hWβ0 hs'.le ⟨ha.1, fun h' => disjoint_left.1 hdisj' ha h'⟩ (hCH z hz) e
    exact hz.2 (Or.inl (by rw [hAeq, ← this]; exact ha))
  have hvL' : ∀ i, (![chartAL W' T, chartBL W' T (frzVR s p.2)] : Fin 2 → ℝ) i ≤ 0 := by
    intro i; fin_cases i
    · exact chartAL_nonpos hW' hT.le
    · exact (chartBL_lt hη' hη'p hW' hW'0 hT.le hvR).le.trans (chartAL_nonpos hW' hT.le)
  have hvR' : ∀ i, 0 ≤ (![chartAR W' T, chartBR W' T (frzVL s p.2)] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact chartAR_nonneg hW' hT.le
    · exact (chartAR_nonneg hW' hT.le).trans (chartAR_lt hη' hη'p hW' hW'0 hT.le hvL).le
  have hcm := isBoundedHarmonicExtension_condMean ![rL, -rL - δ] ![rR, -rR + δ] hvL' hvR'
  have hCopen : IsOpen (H \ (A ∪ G)) := by
    rw [hCeq]
    have h1 := (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWαc ht'.le).inter
      (isOpen_H_diff_negInv_fwdHull hWβ hs'.le)
    convert h1 using 1
    ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
  have hv : InnerProductSpace.HarmonicOnNhd v (H \ (A ∪ G)) := by
    intro z hz
    have hz' := hCH z hz
    have hRd : DifferentiableAt ℂ (revChart Wβ s) z := by
      have hz0 : z ≠ 0 := fun h0 => by
        have := hz.1; rw [h0] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
      have hw := negInv_notMem_fwdHull hz'
      have h1 : DifferentiableAt ℂ negInv z := by
        unfold negInv; exact (differentiableAt_inv hz0).neg
      have h2 : DifferentiableAt ℂ (fwdMap Wβ s) (negInv z) :=
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWβ hs'.le).differentiableAt
          ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWβ hs'.le).mem_nhds hw)
      have h3 : fwdMap Wβ s (negInv z) ≠ 0 := fun h0 => by
        have := QuantumZipper.FwdHolo.mapsTo_fwdMap hWβ hs'.le hw
        rw [h0] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
      have h4 : DifferentiableAt ℂ negInv (fwdMap Wβ s (negInv z)) := by
        unfold negInv; exact (differentiableAt_inv h3).neg
      exact h4.comp z (h2.comp z h1)
    have hGd : DifferentiableOn ℂ (fun z => fwdMap W' T (revChart Wβ s z)) (H \ (A ∪ G)) := by
      intro z₁ hz₁
      have hRd₁ : DifferentiableAt ℂ (revChart Wβ s) z₁ := by
        have hz0 : z₁ ≠ 0 := fun h0 => by
          have := hz₁.1; rw [h0] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
        have hw := negInv_notMem_fwdHull (hCH z₁ hz₁)
        have h1 : DifferentiableAt ℂ negInv z₁ := by
          unfold negInv; exact (differentiableAt_inv hz0).neg
        have h2 : DifferentiableAt ℂ (fwdMap Wβ s) (negInv z₁) :=
          (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWβ hs'.le).differentiableAt
            ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWβ hs'.le).mem_nhds hw)
        have h3 : fwdMap Wβ s (negInv z₁) ≠ 0 := fun h0 => by
          have := QuantumZipper.FwdHolo.mapsTo_fwdMap hWβ hs'.le hw
          rw [h0] at this; exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
        have h4 : DifferentiableAt ℂ negInv (fwdMap Wβ s (negInv z₁)) := by
          unfold negInv; exact (differentiableAt_inv h3).neg
        exact h4.comp z₁ (h2.comp z₁ h1)
      have hfd : DifferentiableAt ℂ (fwdMap W' T) (revChart Wβ s z₁) :=
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW' hT.le).differentiableAt
          ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW' hT.le).mem_nhds (hCA z₁ hz₁))
      exact (hfd.comp z₁ hRd₁).differentiableWithinAt
    have han : AnalyticAt ℂ (fun z => fwdMap W' T (revChart Wβ s z)) z :=
      hGd.analyticAt (hCopen.mem_nhds hz)
    have hcz := hcm.1 _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT.le (hCA z hz))
    have h1 := QuantumZipper.FieldLawler.fl_harmonicAt_comp
      (h := chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T (frzVL s p.2) (frzVR s p.2)) han hcz
    exact h1.sub (hu₀.1 z hz.1)
  have hvb : ∃ M, ∀ z ∈ H \ (A ∪ G), |v z| ≤ M := by
    obtain ⟨C₁, hC₁⟩ := hcm.2.1
    obtain ⟨C₂, hC₂'⟩ := hu₀.2.1
    refine ⟨C₁ + C₂, fun z hz => ?_⟩
    have h1 := hC₁ _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT.le (hCA z hz))
    have h2 := hC₂' z hz.1
    simp only [hvdef]
    calc |chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T (frzVL s p.2) (frzVR s p.2)
            (fwdMap W' T (revChart Wβ s z)) - u₀ z|
        ≤ |chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T (frzVL s p.2) (frzVR s p.2)
            (fwdMap W' T (revChart Wβ s z))| + |u₀ z| := abs_sub _ _
      _ ≤ C₁ + C₂ := add_le_add h1 h2
  have hlim : ∀ x : ℝ, x ∉ E → Tendsto (fun y => w (twoSlitChart Wβ s W' T y) - v (twoSlitChart Wβ s W' T y))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x hx
    refine (hE x hx).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hF' := QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy
    simp only [hvdef, twoSlitChart, revChart_revChartInv hWβ hWβ0 hs'.le hF',
      QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT.le hy]
    ring
  have hEq := hcorp w hw hrep (H \ (A ∪ G)) hCopen subset_rfl _ hΦ v hv hvb E hEfin hlim
  refine ⟨w, hw, hrep, W', hW', hW'0, T, hT, η', hη', hη'p, by rw [hK', hAeq], fun z hz => ?_⟩
  have := hEq hz
  simp only [hvdef] at this
  linarith

end Glue

end InteractingSLE.WangWu
