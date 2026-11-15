/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactGerm
import InteractingSLE.WangWu.ReverseContactGlue
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# The two slit means of the contact step

Packet PROVE-WW-B12. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of
Proposition 4.18 (text dump L1607–1614). Step (S3a) of PROVE-WW-B11's obstruction: the local-set means of the two
stopped slits, identified with the explicit level-line means.

* `not_thresholdCondition_twoSeed`: a nonnegative two-seed marked chain has an admissible seed.
* **`exists_isLocalSetMean_histHull_twoSeed`**: on the space of a frozen coupling of a nonnegative two-seed word, the
  stopped hull `α(0, t]` read from the history has a local-set mean of the centred field `h − u₀`; off the hull it is
  the explicit mean `meanAt − u₀` (Wang–Wu Corollary 3.9 with whole-field identification).
* **`exists_isLocalSetMean_fwdSlit_glue`**: the same mean, read from the first coordinate, is a local-set mean of the
  forward slit on the glued space (`IsLocalSetMean.comp` along `Prod.fst`).
* `eqOn_bhe_reflect_twoSeed`: the boundary harmonic extension of the reflected word, read through `R`, is minus that of
  the word; `reflectField_smoothDist`, `reflectField_centredField_twoSeed`: hence the reflected centred field of the
  reverse coupling is the reflected field minus `u₀`.
* **`exists_isLocalSetMean_revSlit_twoSeed`**: on the space of the reverse coupling, the reflected stopped hull
  `R(β(0, s])` has the reflected explicit mean as a local-set mean of `−h₂ ∘ R − u₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open LawUnique
open LocalSets (IsLocalSetMean germSigma)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

universe u

section TwoSeed

variable {rL rR : ℝ}

/-- **A nonnegative two-seed marked chain has an admissible seed** (its lifetime is infinite almost surely, while at an
inadmissible seed it vanishes). -/
theorem not_thresholdCondition_twoSeed (hL : 0 ≤ rL) (hR : 0 ≤ rR) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsMarkedChain LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ¬ ForceWord.ThresholdCondition (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 0 LP.twoSeedXL LP.twoSeedXR := by
  intro hth
  have hF : ∀ᵐ ω ∂P, False := by
    filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hE,
      hE.2.2.2.2] with ω hω hp
    have h0 := IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hth
    rw [hω.1] at h0
    exact ENNReal.top_ne_zero h0
  obtain ⟨_, hfalse⟩ := hF.exists
  exact hfalse

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The stopped hull of a two-seed coupling has the explicit level-line mean**: the hull `α(0, t]` read from the
history (`t > 0` rational) has a local-set mean of the centred field `h − u₀`, and off the hull it is
`meanAt − u₀` at time `t` (Wang–Wu Corollary 3.9). -/
theorem exists_isLocalSetMean_histHull_twoSeed (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t : ℚ} (ht : 0 < t) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun ω => histHull t (killedHistory W VL VR ζ ω)) (WholeField.centredField h u₀) P g ∧
      ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ histHull t (killedHistory W VL VR ζ ω) →
        g ω φ = ∫ z, (meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · ω) (fun i => (VL i · ω))
          (fun i => (VR i · ω)) (Real.toNNReal t) z - u₀ z) * φ z := by
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hF := isFullLevelLineCoupling_twoSeed hL hR hC
  have hseed := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1
  have htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
    filter_upwards [hseed] with ω hω
    obtain ⟨hζ, ⟨η, hη, -⟩, -⟩ := hω
    exact ⟨η, hζ ▸ hη⟩
  have hτζ : ∀ᵐ ω ∂P, ((Real.toNNReal t : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hseed] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hh0 := WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hAm : Measurable[mΩ, hittingSigma] fun ω => histHull t (killedHistory W VL VR ζ ω) :=
    (measurable_histHull t).comp (measurable_killedHistory hX)
  have hloc : IsLocalSet (fun ω => histHull t (killedHistory W VL VR ζ ω)) (WholeField.centredField h u₀) P :=
    WholeField.IsLocalSet.sub_dist (isLocalSet_histHull_twoSeed hL hR hC ht)
      (WholeField.isHarmonicDistOn_smoothDist hu₀.1)
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  refine ⟨g, hg, ?_⟩
  have hAK : ∀ᵐ ω ∂P, histHull t (killedHistory W VL VR ζ ω) =
      fwdHull (fun s : ℝ => W s.toNNReal ω)
        (((fun _ : Ω => (Real.toNNReal t : WithTop ℝ≥0)) ω).untopD 0 : ℝ≥0) := by
    filter_upwards [ae_histHull_eq_fwdHull hL hR hC.1 ht] with ω hω
    rw [hω]
    rfl
  exact hF.ae_apply_eq_of_isLocalSetMean_hull htr (not_thresholdCondition_twoSeed hL hR hC.1) hu₀ hX
    (isStoppingTime_const (drivingFiltration P hX) (Real.toNNReal t)) hτζ hAm hAK hg

/-- **The forward slit mean on the glued space**: the explicit mean of the forward hull, read from the first
coordinate, is a local-set mean of the forward slit for the centred field on `P ⊗ k(h)`. -/
theorem exists_isLocalSetMean_fwdSlit_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {β : Type*} [MeasurableSpace β] (k : Kernel (DistOn upperHalfPlaneOpens) β) [IsMarkovKernel k]
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t : ℚ} (ht : 0 < t) :
    ∃ g : Ω × β → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × β => histHull t (killedHistory W VL VR ζ p.1))
        (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k h hC.2.1) g ∧
      ∀ᵐ p ∂(glueMeasure P k h hC.2.1), ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ histHull t (killedHistory W VL VR ζ p.1) →
        g p φ = ∫ z, (meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1) (fun i => (VL i · p.1))
          (fun i => (VR i · p.1)) (Real.toNNReal t) z - u₀ z) * φ z := by
  obtain ⟨g, hg, hid⟩ := exists_isLocalSetMean_histHull_twoSeed hL hR hC hu₀ ht
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hAm : Measurable[mΩ, hittingSigma] fun ω => histHull t (killedHistory W VL VR ζ ω) :=
    (measurable_histHull t).comp (measurable_killedHistory hX)
  exact ⟨fun p => g p.1, IsLocalSetMean.comp measurable_fst (glueMeasure_fst (μ := P) k hC.2.1) hAm
    (WholeField.measurable_centredField hC.2.1 u₀) hg, ae_glue_fst k hC.2.1 hid⟩

/-! ### The reflected reverse slit -/

/-- **The harmonic extension of the reflected word, read through `R`, is minus that of the word**:
`−u₀'(−1/z) = u₀(z)` on `ℍ` (the return data of `(r_R; r_L)` are the data of `(r_L; r_R)` off `0`). -/
theorem eqOn_bhe_reflect_twoSeed {u₀ u₀' : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀') :
    EqOn (fun z => -u₀' (negInv z)) u₀ H := by
  rw [forceJumpSet_twoSeed] at hu₀ hu₀'
  have hr := Sec7.StripSysField.isBoundedHarmonicExtension_return 0 0 hu₀'
  rw [returnExcept_zero] at hr
  have hbdd : ∀ {v : ℂ → ℝ}, (∃ C : ℝ, ∀ z ∈ H, |v z| ≤ C) → Bornology.IsBounded (v '' H) := by
    rintro v ⟨C, hC⟩
    exact isBounded_iff_forall_norm_le.2 ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact (hC z hz)⟩
  have heq := InteractingSLE.eqOn_of_tendsto_sub_H {0} hr.1 hu₀.1 (hbdd hr.2.1) (hbdd hu₀.2.1)
    fun x hx => by
      have hx' : x ∉ (({0} : Finset ℝ) : Set ℝ) := by simpa using hx
      have h1 := (hr.2.2 x (by simpa using hx)).sub (hu₀.2.2 x hx')
      rwa [returnData_twoSeed rL rR (by simpa using hx), sub_self] at h1
  intro z hz
  have := heq hz
  simp only [zero_mul, add_zero] at this
  exact this

/-- `R` acts on smooth distributions by `u ↦ −u ∘ R`. -/
theorem reflectField_smoothDist {u : ℂ → ℝ} (hu : ContinuousOn u H) :
    reflectField (smoothDist upperHalfPlaneOpens u) =
      smoothDist upperHalfPlaneOpens (fun z => -u (negInv z)) := by
  have hc : ContinuousOn (fun z => -u (negInv z)) H :=
    (hu.comp continuousOn_negInv fun z hz => negInv_mem_H hz).neg
  ext φ
  rw [reflectField_apply, smoothDist_apply hu, smoothDist_apply hc]
  have h1 := Chart.integral_mul_pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ u
  have h2 : (∫ x, (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ) x * u x) =
      ∫ z, u z * (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ) z :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [h2, h1, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [infinityReturnChart_inv_eq]
  ring

/-- Smooth distributions only see the function on `ℍ`. -/
theorem smoothDist_congr {u v : ℂ → ℝ} (hu : ContinuousOn u H) (hv : ContinuousOn v H) (huv : EqOn u v H) :
    smoothDist upperHalfPlaneOpens u = smoothDist upperHalfPlaneOpens v := by
  ext φ
  rw [smoothDist_apply hu, smoothDist_apply hv]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show φ x * u x = φ x * v x
  by_cases hx : x ∈ H
  · rw [huv hx]
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)
    rw [this, zero_mul, zero_mul]

/-- **The reflected centred field of the reverse coupling** is the reflected field minus the forward `u₀`. -/
theorem reflectField_centredField_twoSeed {Ω₂ : Type*} (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) {u₀ u₀' : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀') (ω : Ω₂) :
    reflectField (WholeField.centredField h₂ u₀' ω) =
      reflectField (h₂ ω) - smoothDist upperHalfPlaneOpens u₀ := by
  have hc' : ContinuousOn u₀' H := fun z hz => (hu₀'.1 z hz).1.continuousAt.continuousWithinAt
  have hc : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hc'' : ContinuousOn (fun z => -u₀' (negInv z)) H :=
    (hc'.comp continuousOn_negInv fun z hz => negInv_mem_H hz).neg
  rw [WholeField.centredField, reflectField_sub, reflectField_smoothDist hc',
    smoothDist_congr hc'' hc (eqOn_bhe_reflect_twoSeed hu₀ hu₀')]

/-- **The reflected reverse slit has the reflected explicit mean.** For a frozen coupling of the reflected word
`(r_R; r_L)`, the reflected stopped hull `R(β(0, s])` read from its history has a local-set mean of `−h₂ ∘ R − u₀`
(`u₀` the harmonic extension of the forward data), equal off the slit to `−meanAt(R z) − u₀(z)`. -/
theorem exists_isLocalSetMean_revSlit_twoSeed (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {s : ℚ} (hs : 0 < s) :
    ∃ g : Ω₂ → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
        (fun ω => reflectField (h₂ ω) - smoothDist upperHalfPlaneOpens u₀) P₂ g ∧
      ∀ᵐ ω ∂P₂, ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) →
        g ω φ = ∫ z, (-meanAt (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (W₂ · ω) (fun i => (VL₂ i · ω))
          (fun i => (VR₂ i · ω)) (Real.toNNReal s) (negInv z) - u₀ z) * φ z := by
  obtain ⟨u₀', hu₀'⟩ := WholeField.exists_bhe 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) LP.twoSeedXL
    LP.twoSeedXR
  obtain ⟨g', hg', hid'⟩ := exists_isLocalSetMean_histHull_twoSeed hR hL hC₂ hu₀' hs
  have hrefl := IsLocalSetMean.reflect (fun ω => histHull_relClosed s (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) hg'
  have hfield : (fun ω => reflectField (WholeField.centredField h₂ u₀' ω)) =
      fun ω => reflectField (h₂ ω) - smoothDist upperHalfPlaneOpens u₀ :=
    funext (reflectField_centredField_twoSeed h₂ hu₀ hu₀')
  rw [hfield] at hrefl
  refine ⟨fun ω => reflectField (g' ω), hrefl, ?_⟩
  have hEq := eqOn_bhe_reflect_twoSeed hu₀ hu₀'
  filter_upwards [hid'] with ω hω φ hφ
  set K := histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) with hK
  set ψ := Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ with hψ
  have hψs : tsupport ψ ⊆ H \ K := by
    refine (tsupport_pushTest_return_subset φ).trans ?_
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hφ hz
    rw [H_diff_image_negInv] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    rw [← hwz, negInv_negInv]
    exact hw
  rw [reflectField_apply, hω ψ hψs]
  have h1 := Chart.integral_mul_pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ
    (fun z => meanAt (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (W₂ · ω) (fun i => (VL₂ i · ω))
      (fun i => (VR₂ i · ω)) (Real.toNNReal s) z - u₀' z)
  rw [h1, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  simp only [infinityReturnChart_inv_eq]
  by_cases hw : w ∈ H
  · have := hEq hw
    simp only at this
    rw [← this]
    ring
  · have : φ w = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (φ.tsupport_subset h)
    rw [this]
    ring

end TwoSeed

end InteractingSLE.WangWu
