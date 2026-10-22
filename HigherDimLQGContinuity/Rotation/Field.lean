import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Sphere.Growth
import HigherDimLQGMetric.LGF.Normalized
import HigherDimLQGMetric.Frozen.NormLGFLawSpec
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rotation of distributions and the whole-space log-correlated field

The pullback is defined on test functions first and then transposed to distributions.
The change of variables for a linear isometry preserves the logarithmic covariance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions Pointwise

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

private def rotCompact (e : Rd d ≃L[ℝ] Rd d) (K : Compacts (Rd d)) :
    Compacts (Rd d) := K.map e.symm e.symm.continuous

private lemma mem_rotCompact_of (e : Rd d ≃L[ℝ] Rd d) (K : Compacts (Rd d))
    {x : Rd d} (hx : e x ∈ (K : Set (Rd d))) :
    x ∈ (rotCompact e K : Set (Rd d)) :=
  ⟨e x, hx, e.symm_apply_apply x⟩

private def testRotPullK (e : Rd d ≃L[ℝ] Rd d) (K : Compacts (Rd d)) :
    𝓓^{⊤}_{K}(Rd d, ℝ) →ₗ[ℝ] 𝓓^{⊤}_{rotCompact e K}(Rd d, ℝ) where
  toFun φ :=
    { toFun := φ ∘ e
      contDiff' := φ.contDiff.comp e.contDiff
      zero_on_compl' := fun _ hx => φ.zero_on_compl
        (fun hK => hx (mem_rotCompact_of e K hK)) }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma iteratedFDeriv_comp_rot (e : Rd d ≃L[ℝ] Rd d)
    {φ : Rd d → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (i : ℕ)
    (x : Rd d) :
    iteratedFDeriv ℝ i (φ ∘ e) x =
      (iteratedFDeriv ℝ i φ (e x)).compContinuousLinearMap
        fun _ => (e : Rd d →L[ℝ] Rd d) :=
  (e : Rd d →L[ℝ] Rd d).iteratedFDeriv_comp_right hφ x (by exact_mod_cast le_top)

private lemma continuous_testRotPullK (e : Rd d ≃L[ℝ] Rd d)
    (K : Compacts (Rd d)) : Continuous (testRotPullK e K) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  let Ψ := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
      (E := fun _ : Fin i => Rd d) (E₁ := fun _ : Fin i => Rd d) (F := ℝ)
      (fun _ => (e : Rd d →L[ℝ] Rd d))).compLeftContinuousBounded (Rd d)
  have key : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ testRotPullK e K) =
      (fun g => (Ψ g).compContinuous ⟨e, e.continuous⟩) ∘
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := by
    funext φ
    ext x : 1
    simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rw [BoundedContinuousFunction.compContinuous_apply,
      ContinuousLinearMap.compLeftContinuousBounded_apply,
      ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact iteratedFDeriv_comp_rot e φ.contDiff i x
  rw [key]
  exact ((BoundedContinuousFunction.continuous_compContinuous _).comp Ψ.continuous).comp
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous

private lemma hasCompactSupport_comp_rot (e : Rd d ≃L[ℝ] Rd d)
    {φ : Rd d → ℝ} (hφ : HasCompactSupport φ) : HasCompactSupport (φ ∘ e) :=
  hφ.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding

/-- Pullback of test functions by a linear equivalence, as a continuous linear map. -/
def testRotPull (O : Rd d ≃ₗᵢ[ℝ] Rd d) : TestRd d →L[ℝ] TestRd d :=
  let e : Rd d ≃L[ℝ] Rd d := O.symm.toContinuousLinearEquiv
  TestFunction.mkCLM ℝ
    (fun φ => ⟨φ ∘ e, φ.contDiff.comp e.contDiff,
      hasCompactSupport_comp_rot e φ.hasCompactSupport, subset_univ _⟩)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun K _ => by
      have : (fun φ : TestRd d => (⟨φ ∘ e, φ.contDiff.comp e.contDiff,
          hasCompactSupport_comp_rot e φ.hasCompactSupport, subset_univ _⟩ : TestRd d)) ∘
          TestFunction.ofSupportedIn (subset_univ (K : Set (Rd d))) =
          TestFunction.ofSupportedInCLM ℝ (subset_univ (rotCompact e K : Set (Rd d))) ∘
            testRotPullK e K := by
        funext φ; ext x; rfl
      rw [this]
      exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp
        (continuous_testRotPullK e K))

@[simp] lemma testRotPull_apply (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (φ : TestRd d) (x : Rd d) : testRotPull O φ x = φ (O.symm x) := rfl

/-- The distribution corresponding to `g(O ·)`. -/
def rotDistRd (O : Rd d ≃ₗᵢ[ℝ] Rd d) (g : DistRd d) : DistRd d :=
  g.comp (testRotPull O)

@[simp] lemma rotDistRd_apply (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (g : DistRd d) (φ : TestRd d) : rotDistRd O g φ = g (testRotPull O φ) := rfl

theorem measurable_rotDistRd (O : Rd d ≃ₗᵢ[ℝ] Rd d) : Measurable (rotDistRd O) :=
  (HigherDimLQGMetric.measurable_distOn_iff).2
    fun φ => HigherDimLQGMetric.measurable_distOn_apply (testRotPull O φ)

private lemma integral_comp_rot (O : Rd d ≃ₗᵢ[ℝ] Rd d) (F : Rd d → ℝ) :
    ∫ x, F (O x) = ∫ x, F x :=
  O.measurePreserving.integral_comp O.toHomeomorph.measurableEmbedding F

private lemma integral_testRotPull (O : Rd d ≃ₗᵢ[ℝ] Rd d) (φ : TestRd d) :
    ∫ x, testRotPull O φ x = ∫ x, φ x := by
  simp only [testRotPull_apply]
  exact integral_comp_rot O.symm fun x => φ x

private def testRotPull0 (O : Rd d ≃ₗᵢ[ℝ] Rd d) (φ : TestRd0 d) : TestRd0 d :=
  ⟨testRotPull O φ.1, by rw [integral_testRotPull, φ.2]⟩

private lemma logCovRd_comp_rot (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (φ ψ : Rd d → ℝ) :
    logCovRd (fun x => φ (O x)) (fun y => ψ (O y)) = logCovRd φ ψ := by
  unfold logCovRd
  rw [← integral_comp_rot O.symm]
  congr 1
  funext x
  rw [← integral_comp_rot O.symm]
  congr 1
  funext y
  simp only [O.apply_symm_apply]
  rw [← O.norm_map (O.symm x - O.symm y)]
  simp only [map_sub, O.apply_symm_apply]

private lemma logCovRd_testRotPull0 (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (φ ψ : TestRd0 d) :
    logCovRd (testRotPull0 O φ).1 (testRotPull0 O ψ).1 = logCovRd φ.1 ψ.1 := by
  change logCovRd (fun x => φ.1 (O.symm x)) (fun y => ψ.1 (O.symm y)) = _
  exact logCovRd_comp_rot O.symm _ _

/-- Isometric pullback preserves the whole-space LGF law modulo constants. -/
theorem isWholeSpaceLGF_rotDistRd {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) :
    IsWholeSpaceLGF (fun ω => rotDistRd O (h ω)) P where
  measurable := (measurable_rotDistRd O).comp hh.measurable
  gaussian := hh.gaussian.comp_right (testRotPull0 O)
  centered := fun φ => hh.centered (testRotPull0 O φ)
  covariance_eq := fun φ ψ =>
    (hh.covariance_eq (testRotPull0 O φ) (testRotPull0 O ψ)).trans
      (logCovRd_testRotPull0 O φ ψ)

private lemma rot_sector (O : Rd d ≃ₗᵢ[ℝ] Rd d) (A : Set (Rd d)) :
    Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ O ⁻¹' A) =
      O ⁻¹' (Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ A)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, t, ht, rfl⟩ := mem_smul.1 hx
    change O (c • t) ∈ Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ A)
    refine mem_smul.2 ⟨c, hc, O t, ⟨?_, ht.2⟩, by simp⟩
    simpa only [mem_sphere_zero_iff_norm, O.norm_map] using ht.1
  · intro hx
    obtain ⟨c, hc, t, ht, heq⟩ := mem_smul.1 hx
    refine mem_smul.2 ⟨c, hc, O.symm t, ⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_sphere_zero_iff_norm, O.symm.norm_map] using ht.1
    · simpa only [Set.mem_preimage, O.apply_symm_apply] using ht.2
    · apply O.injective
      simpa only [map_smul, O.apply_symm_apply] using heq

/-- The normalized sphere measure is invariant under linear isometries. -/
theorem map_linearIsometry_unitSphereProb (hd : 1 ≤ d)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) :
    (unitSphereProb d).map O = unitSphereProb d := by
  ext A hA
  rw [Measure.map_apply O.continuous.measurable hA,
    unitSphereProb_apply_eq hd (O.continuous.measurable hA),
    unitSphereProb_apply_eq hd hA, rot_sector]
  have heq := congrArg
    (fun μ : Measure (Rd d) => μ (Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ A)))
    O.measurePreserving.map_eq
  have hmap := O.toHomeomorph.measurableEmbedding.map_apply
    (volume : Measure (Rd d)) (Ioo (0 : ℝ) 1 • (sphere (0 : Rd d) 1 ∩ A))
  convert congrArg (fun x : ENNReal => (volume (ball (0 : Rd d) 1))⁻¹ * x)
    (hmap.symm.trans heq) using 1
  simp only [LinearIsometryEquiv.coe_toHomeomorph]

private lemma bumpTest_rot (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (n : ℕ) (x : Rd d) :
    testRotPull O (bumpTest n x) = bumpTest n (O x) := by
  apply TestFunction.ext
  intro y
  rw [testRotPull_apply, HigherDimLQGMetric.bumpTest_apply,
    HigherDimLQGMetric.bumpTest_apply]
  congr 1
  apply HigherDimLQGMetric.radialProfile_eq_of_norm_eq
  simp only [norm_smul, Real.norm_eq_abs]
  congr 1
  rw [← O.norm_map (O.symm y - x)]
  simp only [map_sub, O.apply_symm_apply]

private lemma sphereAvgSeq_rotDistRd (hd : 1 ≤ d)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (g : DistRd d) (r : ℝ)
    (z : Rd d) (n : ℕ) :
    sphereAvgSeq (rotDistRd O g) r z n = sphereAvgSeq g r (O z) n := by
  simp only [sphereAvgSeq, rotDistRd_apply, bumpTest_rot]
  have hcont := HigherDimLQGMetric.continuous_apply_bumpTest_affine g n r (O z)
  calc
    ∫ u, g (bumpTest n (O (z + r • u))) ∂(unitSphereProb d) =
        ∫ u, g (bumpTest n (O z + r • u)) ∂((unitSphereProb d).map O) := by
      rw [integral_map O.continuous.measurable.aemeasurable hcont.aestronglyMeasurable]
      congr 1
      funext u
      simp only [map_add, map_smul]
    _ = ∫ u, g (bumpTest n (O z + r • u)) ∂(unitSphereProb d) := by
      rw [map_linearIsometry_unitSphereProb hd O]

/-- Rotation commutes with sphere averages, including the totalized limit convention. -/
theorem sphereAvg_rotDistRd (hd : 1 ≤ d) (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (g : DistRd d) (r : ℝ) (z : Rd d) :
    sphereAvg (rotDistRd O g) r z = sphereAvg g r (O z) := by
  simp only [HigherDimLQGMetric.sphereAvg_eq_limUnder]
  congr 1
  funext n
  exact sphereAvgSeq_rotDistRd hd O g r z n

/-- Pulling the normalized LGF back by an isometry preserves its law. -/
theorem map_rotDistRd_normLGFLaw (hd : 2 ≤ d)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) :
    (normLGFLaw d).map (rotDistRd O) = normLGFLaw d := by
  let μ := normLGFLaw d
  have hspec := normLGFLaw_spec d hd
  have hrot : IsNormalizedLGF (rotDistRd O) μ := by
    refine ⟨isWholeSpaceLGF_rotDistRd hspec.2.1.1 O, ?_⟩
    filter_upwards [hspec.2.1.2] with g hg
    simpa only [sphereAvg_rotDistRd (by omega) O, map_zero, id_eq] using hg
  have hmap := hrot.map_id
  have hprobMap : IsProbabilityMeasure (μ.map (rotDistRd O)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_rotDistRd O).aemeasurable).2 hspec.1
  simpa only [μ] using hspec.2.2 (μ.map (rotDistRd O)) hprobMap hmap

end HigherDimLQGContinuity
