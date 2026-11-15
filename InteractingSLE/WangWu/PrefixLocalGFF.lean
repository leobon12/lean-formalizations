/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.PrefixLocal
import InteractingSLE.Spec.Coupling.ResampleBridge
import InteractingSLE.Spec.Restart.ChartGauss
import InteractingSLE.WangWu.CouplingMainZ
import InteractingSLE.WangWu.CouplingBridge

/-!
# Wang–Wu Corollary 3.9: a full level-line coupling is a frozen optional hull coupling

Packet PROVE-WW-B8. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Definition 1.5 and
Corollary 3.9 (text dump L147–156, L916–927). PROVE-WW-A's `IsFullLevelLineCoupling.condExp_cexp_eq_of_disjoint`
(`CouplingBridge`) recorded what separates Definition 1.5 from the frozen `IsOptionalHullCoupling 4`: "the
zero-boundary GFF law of `F − 𝔥₀` (the `τ = 0` case of the kernel identity …) and the local-set property of `K_τ` (the
document's Corollary 3.9)". Both are proved here for couplings with an admissible seed whose driver almost surely has
a continuous generating trace through its lifetime (the trace gives the zero area used to identify the retained
energy with the dual Dirichlet norm):

* `IsFullLevelLineCoupling.integral_cexp_centredField`: `E[e^{i(F − u₀, φ)}] = exp(−½ ‖φ‖²_{H⁻¹(ℍ)})` (the kernel at
  `τ = 0`, where the frozen mean is the seed's `condMean = u₀` and the retained energy is the dual norm on `ℍ`);
* `IsFullLevelLineCoupling.isZeroBoundaryGFF_centredField`: hence `F − u₀` is a zero-boundary GFF on `ℍ` (its law is
  the reference law `Coupling.zbLaw`, by uniqueness of characteristic functionals);
* **`IsFullLevelLineCoupling.isOptionalHullCoupling`**: the full coupling satisfies `IsOptionalHullCoupling 4`
  (the local-set clause is `IsFullLevelLineCoupling.isLocalSet_hull`, `PrefixLocal.lean`).

Consequently the whole history-marked germ machinery of the frozen coupling (`WholeField.ae_condExp_germSigma_hull_eq`,
`WholeField.isHistoryAvoidanceLocal_hull`, …) applies to full level-line couplings.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace QuantumZipper
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE.WangWu

open LQGMetric LocalSets

/-! ### Preliminaries -/

section Prelim

/-- At an admissible seed the lifetime of an integrated path is positive. -/
theorem IsIntegratedSLEPath.lifetime_pos {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) : 0 < ζ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hp
  exact pos_iff_ne_zero.2 fun h0 => hseed (h19 h0)

/-- At an admissible seed the left positions are `≤ 0` and the right positions `≥ 0`. -/
theorem IsIntegratedSLEPath.seed_signs {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) : (∀ i, xL i ≤ 0) ∧ ∀ i, 0 ≤ xR i := by
  have hζ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := by simpa using IsIntegratedSLEPath.lifetime_pos hp hseed
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, hvLw, hwvR, -⟩ := hp
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h := hvLw 0 hζ i
    rwa [hvL0 i, hw0] at h
  · have h := hwvR 0 hζ i
    rwa [hvR0 i, hw0] at h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The characteristic functional of a zero-boundary GFF on `ℍ`: `E[e^{i(g, φ)}] = exp(−½ ‖φ‖²_{H⁻¹(ℍ)})`. -/
theorem integral_cexp_of_isZeroBoundaryGFF {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsZeroBoundaryGFF upperHalfPlaneOpens g P) (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (g ω φ : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ) : ℝ) : ℂ) := by
  have hm : AEMeasurable (fun ω => g ω φ) P := (hg.process.measurable φ).aemeasurable
  rw [GFF.integral_exp_I_mul_of_hasGaussianLaw (hg.process.gaussian.hasGaussianLaw_eval φ)
    (hg.process.centered φ), ← covariance_self hm, hg.process.covariance_eq φ φ]

end Prelim

/-! ### The field law -/

section Law

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {F : Ω → DistOn upperHalfPlaneOpens}

/-- The seed mean `condMean` is the bounded harmonic extension of the time-zero data: any bounded harmonic extension
`u₀` agrees with it on `ℍ` (positions on the correct sides of `0`). -/
theorem eqOn_condMean_of_isBoundedHarmonicExtension (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ i, 0 ≤ xR i)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    EqOn (condMean ρL ρR xL xR) u₀ H :=
  Impl.eqOn_of_isBoundedHarmonicExtension (Impl.forceJumpSet_finite (Ito.weightWord ρL ρR) xL xR) hu₀
    (isBoundedHarmonicExtension_condMean ρL ρR hxL hxR)

/-- **The kernel at `τ = 0`**: `E[e^{i(F − u₀, φ)}] = exp(−½ ‖φ‖²_{H⁻¹(ℍ)})` for a full level-line coupling with an
admissible seed whose driver almost surely has a continuous generating trace through its lifetime. -/
theorem IsFullLevelLineCoupling.integral_cexp_centredField [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (WholeField.centredField F u₀ ω φ : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ) : ℝ) : ℂ) := by
  obtain ⟨hE, hFm, hX, hK⟩ := hF
  set τ₀ : Ω → WithTop ℝ≥0 := fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) with hτ₀
  have hτ : IsStoppingTime (drivingFiltration P hX) τ₀ := isStoppingTime_const _ _
  have hpos : ∀ᵐ ω ∂P, 0 < ζ ω := by
    filter_upwards [hE.2.2.2.2] with ω hp using IsIntegratedSLEPath.lifetime_pos hp hseed
  have hτζ : ∀ᵐ ω ∂P, (τ₀ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hpos] with ω hω
    exact hω
  have hkern := hK τ₀ hτ hτζ φ
  have h𝒢 : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  set a : ℝ := ∫ z, u₀ z * φ z with ha
  set q : ℝ := zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ with hq
  -- almost surely the kernel at `0` is the constant `e^{ia − q/2}`
  have hconst : ∀ᵐ ω ∂P, (P[fun ω' => Complex.exp (Complex.I * (F ω' φ : ℂ)) | hτ.measurableSpace]) ω =
      Complex.exp (Complex.I * (a : ℂ) - (((1 / 2 : ℝ) * q : ℝ) : ℂ)) := by
    filter_upwards [hkern, hE.2.2.2.2, hpos, htr] with ω hk hp hζ htrω
    rw [hk]
    have ht0 : (τ₀ ω).untopD 0 = 0 := by simp [hτ₀]
    rw [ht0]
    obtain ⟨-, hvL0, hvR0, -, -, -, -, hvLw, hwvR, -⟩ := id hp
    have hxL : ∀ i, xL i ≤ 0 := fun i => by
      have h := hvLw 0 (by simpa using hζ) i
      rwa [hvL0 i, hp.1] at h
    have hxR : ∀ i, 0 ≤ xR i := fun i => by
      have h := hwvR 0 (by simpa using hζ) i
      rwa [hvR0 i, hp.1] at h
    have hmean : ∫ z, frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) 0 z * φ z = a := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ H
      · simp only
        rw [frozenMean_zero_eq hp hζ hz, eqOn_condMean_of_isBoundedHarmonicExtension hxL hxR hu₀ hz]
      · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (φ.tsupport_subset h)
        simp [this]
    obtain ⟨η, hη⟩ := htrω
    have hζ' : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by simpa using hζ
    have himg : η '' Icc 0 (0 : ℝ≥0) = {0} := by
      rw [Icc_self, image_singleton, hη.1]
    have harea : volume (η '' Icc 0 (0 : ℝ≥0) ∩ H) = 0 := by
      rw [himg]
      exact measure_mono_null inter_subset_left (measure_singleton 0)
    have henergy := zeroGFFTestCov_compl_image_eq_retainedGreenEnergy hη hp.2.2.2.1 hp.1 hζ' harea φ
    have hH : H \ η '' Icc 0 (0 : ℝ≥0) = (upperHalfPlaneOpens : Set ℂ) := by
      rw [himg]
      ext z
      simp only [Set.mem_sdiff, mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · intro hz
        exact ⟨hz, fun h0 => by
          have : (0 : ℝ) < z.im := hz
          rw [h0] at this
          simp at this⟩
    rw [hH] at henergy
    rw [hmean, ← henergy]
  have hint : Integrable (fun ω => Complex.exp (Complex.I * (F ω φ : ℂ))) P :=
    Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).comp hFm)).aestronglyMeasurable
      1 (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  have hF0 : ∫ ω, Complex.exp (Complex.I * (F ω φ : ℂ)) ∂P =
      Complex.exp (Complex.I * (a : ℂ) - (((1 / 2 : ℝ) * q : ℝ) : ℂ)) := by
    rw [← integral_condExp h𝒢, integral_congr_ae hconst, integral_const, probReal_univ, one_smul]
  have hcen : (fun ω => Complex.exp (Complex.I * (WholeField.centredField F u₀ ω φ : ℂ))) =
      fun ω => Complex.exp (-(Complex.I * (a : ℂ))) * Complex.exp (Complex.I * (F ω φ : ℂ)) := by
    funext ω
    rw [WholeField.centredField_apply F hu₀.1, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hcen, integral_const_mul, hF0, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **The centred field of a full level-line coupling is a zero-boundary GFF on `ℍ`** (admissible seed, almost surely
a continuous generating trace through the lifetime). -/
theorem IsFullLevelLineCoupling.isZeroBoundaryGFF_centredField [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField F u₀) P := by
  have hm : Measurable (WholeField.centredField F u₀) := WholeField.measurable_centredField hF.2.1 u₀
  have hZ := Coupling.isZeroBoundaryGFF_zbLaw (D := upperHalfPlaneOpens) subset_rfl
  have hlaw : P.map (WholeField.centredField F u₀) = Coupling.zbLaw upperHalfPlaneOpens := by
    have : IsProbabilityMeasure (P.map (WholeField.centredField F u₀)) :=
      (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
    refine Coupling.eq_of_integral_cexp fun ψ => ?_
    rw [integral_map hm.aemeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply ψ)).aestronglyMeasurable,
      hF.integral_cexp_centredField htr hseed hu₀ ψ]
    have := integral_cexp_of_isZeroBoundaryGFF hZ ψ
    simpa using this.symm
  refine ⟨hm, ?_⟩
  have hX : IsZBGFFProcess upperHalfPlaneOpens (fun φ (g : DistOn upperHalfPlaneOpens) => g φ)
      (P.map (WholeField.centredField F u₀)) := by
    rw [hlaw]
    exact hZ.process
  exact Restart.isZBGFFProcess_comp hm hX

/-! ### Corollary 3.9 in frozen form -/

/-- **Wang–Wu Corollary 3.9 in the frozen form**: a full level-line coupling (Definition 1.5) with an admissible seed
whose driver almost surely has a continuous generating trace through its lifetime satisfies the optional hull
specification of the frozen Theorem 1.1 at `κ = 4`: the centred field is a zero-boundary GFF on `ℍ`, and at every
stopping time `τ < ζ` the hull `K_τ` is a local set and the field off the hull has the frozen conditional law. -/
theorem IsFullLevelLineCoupling.isOptionalHullCoupling [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ F := by
  obtain ⟨ω₀, hp₀⟩ := hF.1.2.2.2.2.exists
  obtain ⟨hxL, hxR⟩ := IsIntegratedSLEPath.seed_signs hp₀ hseed
  have hu₀ := isBoundedHarmonicExtension_condMean ρL ρR hxL hxR
  refine ⟨hF.1, hF.2.1, fun u hu => ?_, ?_⟩
  · have h := (hF.isZeroBoundaryGFF_centredField htr hseed hu).process
    simpa only [WholeField.centredField_apply F hu.1] using h
  · obtain ⟨hX, hC⟩ := hF.condExp_cexp_eq_of_disjoint
    exact ⟨hX, fun τ hτ hτζ => ⟨hF.isLocalSet_hull htr hu₀.1
      (hF.isZeroBoundaryGFF_centredField htr hseed hu₀) hX hτ hτζ, hC τ hτ hτζ⟩⟩

end Law

end InteractingSLE.WangWu
