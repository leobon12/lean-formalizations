import SupercriticalConformalCovariance.Rotation.MetricV
import LQGMetric.Papers.GM.S1.Dilate

set_option autoImplicit false
noncomputable section

open MeasureTheory Topology Set
open scoped Distributions ENNReal
open LQGMetric
open SupercriticalLQGUniqueness

namespace SupercriticalConformalCovariance.Rotation

private def localRotCLE (a : ℂ) (ha : a ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  GaussianLQG.mulCLE a⁻¹ (inv_ne_zero ha)

/-- Pull a test function on the inverse-rotated open set back to `U`. -/
private def rotPullFun (a : ℂ) (ha : a ≠ 0) (U : TopologicalSpace.Opens ℂ)
    (φ : TestOn (rotOpen a U)) : TestOn U :=
  let e := localRotCLE a ha
  ⟨φ ∘ e, φ.contDiff.comp e.contDiff,
    φ.hasCompactSupport.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding,
    (tsupport_comp_subset_preimage _ e.continuous).trans (by
      intro x hx
      have hφ : e x ∈ (rotOpen a U : Set ℂ) := φ.tsupport_subset hx
      change a * (a⁻¹ * x) ∈ U at hφ
      rw [mul_inv_cancel_left₀ ha] at hφ
      exact hφ)⟩

private def rotPull (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) :
    TestOn (rotOpen a U) →L[ℝ] TestOn U :=
  let e := localRotCLE a ha
  TestFunction.mkCLM ℝ (rotPullFun a ha U)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun K hK => by
      have hsub : (GaussianLQG.cleK e K : Set ℂ) ⊆ U := by
        rintro x ⟨y, hy, rfl⟩
        have hφ : y ∈ (rotOpen a U : Set ℂ) := hK hy
        have he : e.symm y = a * y := by
          apply e.injective
          rw [e.apply_symm_apply]
          change y = a⁻¹ * (a * y)
          rw [inv_mul_cancel_left₀ ha]
        rw [he]
        exact hφ
      have key : (rotPullFun a ha U ∘ TestFunction.ofSupportedIn hK) =
          TestFunction.ofSupportedInCLM ℝ hsub ∘ GaussianLQG.clePullK e K := by
        funext φ; ext x; rfl
      rw [key]
      exact (TestFunction.ofSupportedInCLM ℝ hsub).continuous.comp
        (GaussianLQG.continuous_clePullK e K))

def rotDistOn (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) (k : DistOn U) :
    DistOn (rotOpen a U) :=
  k.comp (rotPull a ha U)

theorem measurable_rotDistOn (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) :
    Measurable (rotDistOn a ha U) :=
  measurable_distOn_iff.2 fun φ =>
    measurable_distOn_apply (rotPull a ha U φ)

theorem restrictTo_rotDist (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) (h : DistC) :
    restrictTo (rotOpen a U) (GaussianLQG.rotDist a h) =
      rotDistOn a ha U (restrictTo U h) := by
  apply DFunLike.ext
  intro φ
  change GaussianLQG.rotDist a h
      (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
        (Ω₁ := rotOpen a U) (Ω₂ := ⊤) φ) =
    h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (Ω₁ := U) (Ω₂ := ⊤) (rotPull a ha U φ))
  rw [GaussianLQG.rotDist_apply]
  apply congrArg h
  apply TestFunction.ext
  intro x
  rw [GaussianLQG.testRot_apply ha, TestFunction.monoCLM_apply,
    TestFunction.monoCLM_apply]
  simp only [le_refl, le_top, and_self, ite_true]
  rfl

private theorem localRot_mem_iff (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) (z : ℂ) :
    a⁻¹ * z ∈ (rotOpen a U : Set ℂ) ↔ z ∈ U := by
  change a * (a⁻¹ * z) ∈ U ↔ z ∈ U
  rw [mul_inv_cancel_left₀ ha]

private def rotPair (a : ℂ) (ha : a ≠ 0)
    (U : TopologicalSpace.Opens ℂ) :
    (↥(U : Set ℂ) × ↥(U : Set ℂ)) →
      (↥(rotOpen a U : Set ℂ) × ↥(rotOpen a U : Set ℂ)) :=
  fun p =>
    (⟨a⁻¹ * p.1.1, (localRot_mem_iff a ha U _).2 p.1.2⟩,
     ⟨a⁻¹ * p.2.1, (localRot_mem_iff a ha U _).2 p.2.2⟩)

theorem ae_rotatedAssignment_local
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusCont h P) {a : ℂ} (ha : ‖a‖ = 1)
    (U : TopologicalSpace.Opens ℂ) :
    ∃ F : DistOn U →
        (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞),
      Measurable F ∧
        ∀ᵐ ω ∂P,
          (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D
            (h ω)).internal (U : Set ℂ) = F (restrictTo U (h ω)) := by
  let ha0 := GaussianLQG.ne_zero_of_norm_eq_one ha
  have hg := isGFFPlusCont_rotDist hh ha
  obtain ⟨F, hFm, hFa⟩ :=
    hD.2.2.1 P (fun ω => GaussianLQG.rotDist a (h ω)) hg (rotOpen a U)
  let F' : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞) :=
    fun k p => F (rotDistOn a ha0 U k) (rotPair a ha0 U p)
  have hFm' : Measurable F' := by
    refine measurable_pi_iff.2 fun p => ?_
    exact (measurable_pi_apply (rotPair a ha0 U p)).comp
      (hFm.comp (measurable_rotDistOn a ha0 U))
  refine ⟨F', hFm', ?_⟩
  filter_upwards [hFa] with ω hω
  funext p
  change (rotMetric a ha0 (D (GaussianLQG.rotDist a (h ω)))).internal U p =
    F (rotDistOn a ha0 U (restrictTo U (h ω))) (rotPair a ha0 U p)
  rw [internal_rotMetric (D (GaussianLQG.rotDist a (h ω))) a ha0
    (U : Set ℂ) (rotOpen a U : Set ℂ) (localRot_mem_iff a ha0 U)]
  rw [hω, restrictTo_rotDist a ha0 U]
  rfl

theorem isStrong_rotatedAssignment
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {a : ℂ} (ha : ‖a‖ = 1) :
    IsStrongLQGMetric ξ Q
      (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D) := by
  unfold SupercriticalLQGUniqueness.IsStrongLQGMetric
  refine ⟨measurable_rotatedAssignment a _ hD.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω mΩ P iP h hh
    exact ae_rotatedAssignment_isLengthSpace hD P h hh ha
  · intro Ω mΩ P iP h hh U
    exact ae_rotatedAssignment_local hD P h hh ha U
  · intro Ω mΩ P iP h hh
    exact ae_rotatedAssignment_weyl hD P h hh ha
  · intro Ω mΩ P iP h hh r z
    exact ae_rotatedAssignment_coord hD P h hh ha r z
  · intro Ω mΩ P iP h hh U hU K₁ K₂ hc₁ hc₂ hconn₁ hconn₂ hn₁ hn₂
      hsub₁ hsub₂ hdisj
    exact ae_rotatedAssignment_finiteSetDist hD P h hh ha U hU K₁ K₂
      hc₁ hc₂ hconn₁ hconn₂ hn₁ hn₂ hsub₁ hsub₂ hdisj


end SupercriticalConformalCovariance.Rotation
