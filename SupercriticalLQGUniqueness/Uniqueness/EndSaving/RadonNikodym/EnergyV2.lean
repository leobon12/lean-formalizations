import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.RNWindowV2




 





set_option autoImplicit false
noncomputable section
open MeasureTheory Set Laplacian
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
open LQGMetric (TestC)

private theorem cmTest_add (φ ψ : TestC) :
    LQGMetric.cmTest (φ + ψ) = LQGMetric.cmTest φ + LQGMetric.cmTest ψ := by
  ext z
  have hφ : ContDiffAt ℝ 2 (φ : ℂ → ℝ) z :=
    ((φ.contDiff.of_le (by simp)).contDiffAt)
  have hψ : ContDiffAt ℝ 2 (ψ : ℂ → ℝ) z :=
    ((ψ.contDiff.of_le (by simp)).contDiffAt)
  change -(2 * Real.pi)⁻¹ * Δ ((φ : ℂ → ℝ) + ψ) z =
    -(2 * Real.pi)⁻¹ * Δ (φ : ℂ → ℝ) z +
      -(2 * Real.pi)⁻¹ * Δ (ψ : ℂ → ℝ) z
  rw [hφ.laplacian_add hψ]
  ring

private theorem energy_eq_integral_cmTest (φ : TestC) :
    LQGMetric.gradEnergy φ = ∫ x, LQGMetric.cmTest φ x * φ x := by
  rw [← LQGMetric.logCov_cmTest_cmTest,
    LQGMetric.logCov_cmTest_right]

private theorem integrable_cmTest_mul (φ ψ : TestC) :
    Integrable (fun x : ℂ => LQGMetric.cmTest φ x * ψ x) :=
  ((LQGMetric.cmTest φ).continuous.mul ψ.continuous).integrable_of_hasCompactSupport
    (LQGMetric.cmTest φ).hasCompactSupport.mul_right

 
theorem integral_cmTest_mul_eq_zero_of_disjoint (φ ψ : TestC)
    (hdisj : Disjoint (tsupport (φ : ℂ → ℝ)) (tsupport (ψ : ℂ → ℝ))) :
    (∫ x : ℂ, LQGMetric.cmTest φ x * ψ x) = 0 := by
  have hpoint : ∀ x : ℂ, LQGMetric.cmTest φ x * ψ x = 0 := by
    intro x
    by_cases hx : x ∈ tsupport (φ : ℂ → ℝ)
    · have hy : x ∉ tsupport (ψ : ℂ → ℝ) :=
        fun hy => Set.disjoint_left.mp hdisj hx hy
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    · rw [LQGMetric.cmTest_apply,
        QuantumZipper.K3.laplacian_eq_zero_of_notMem_tsupport hx]
      ring
  calc
    (∫ x : ℂ, LQGMetric.cmTest φ x * ψ x) = ∫ _x : ℂ, (0 : ℝ) :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = 0 := by simp only [integral_zero]

 

theorem gradEnergy_add_of_disjoint (φ ψ : TestC)
    (hdisj : Disjoint (tsupport (φ : ℂ → ℝ)) (tsupport (ψ : ℂ → ℝ))) :
    LQGMetric.gradEnergy (φ + ψ) =
      LQGMetric.gradEnergy φ + LQGMetric.gradEnergy ψ := by
  change LQGMetric.gradEnergy (⇑(φ + ψ)) =
    LQGMetric.gradEnergy φ + LQGMetric.gradEnergy ψ
  rw [energy_eq_integral_cmTest (φ + ψ), energy_eq_integral_cmTest φ,
    energy_eq_integral_cmTest ψ, cmTest_add]
  have hfun : (fun x : ℂ =>
      (LQGMetric.cmTest φ + LQGMetric.cmTest ψ) x * (φ + ψ) x) =
      fun x : ℂ =>
        (LQGMetric.cmTest φ x * φ x + LQGMetric.cmTest φ x * ψ x) +
          (LQGMetric.cmTest ψ x * φ x + LQGMetric.cmTest ψ x * ψ x) := by
    funext x
    change (LQGMetric.cmTest φ x + LQGMetric.cmTest ψ x) *
      (φ x + ψ x) = _
    ring
  rw [hfun]
  calc
    _ = (∫ x : ℂ, LQGMetric.cmTest φ x * φ x +
          LQGMetric.cmTest φ x * ψ x) +
        (∫ x : ℂ, LQGMetric.cmTest ψ x * φ x +
          LQGMetric.cmTest ψ x * ψ x) :=
      integral_add ((integrable_cmTest_mul φ φ).add (integrable_cmTest_mul φ ψ))
        ((integrable_cmTest_mul ψ φ).add (integrable_cmTest_mul ψ ψ))
    _ = _ := by
      rw [integral_add (integrable_cmTest_mul φ φ) (integrable_cmTest_mul φ ψ),
        integral_add (integrable_cmTest_mul ψ φ) (integrable_cmTest_mul ψ ψ),
        integral_cmTest_mul_eq_zero_of_disjoint φ ψ hdisj,
        integral_cmTest_mul_eq_zero_of_disjoint ψ φ hdisj.symm]
      ring

 
theorem cmDensity_add_of_disjoint (φ ψ : TestC)
    (hdisj : Disjoint (tsupport (φ : ℂ → ℝ)) (tsupport (ψ : ℂ → ℝ)))
    (g : LQGMetric.DistC) :
    LQGMetric.cmDensity (φ + ψ) (LQGMetric.pair0 g) =
      LQGMetric.cmDensity φ (LQGMetric.pair0 g) *
        LQGMetric.cmDensity ψ (LQGMetric.pair0 g) := by
  have hpair : LQGMetric.pair0 g (LQGMetric.cmTest0 (φ + ψ)) =
      LQGMetric.pair0 g (LQGMetric.cmTest0 φ) +
        LQGMetric.pair0 g (LQGMetric.cmTest0 ψ) := by
    change g (LQGMetric.cmTest (φ + ψ)) =
      g (LQGMetric.cmTest φ) + g (LQGMetric.cmTest ψ)
    rw [cmTest_add]
    exact map_add g _ _
  have henergy : LQGMetric.gradEnergy (⇑(φ + ψ)) =
      LQGMetric.gradEnergy φ + LQGMetric.gradEnergy ψ :=
    gradEnergy_add_of_disjoint φ ψ hdisj
  rw [LQGMetric.cmDensity, LQGMetric.cmDensity, LQGMetric.cmDensity,
    hpair, henergy]
  have he : (LQGMetric.pair0 g (LQGMetric.cmTest0 φ) +
      LQGMetric.pair0 g (LQGMetric.cmTest0 ψ)) -
      (LQGMetric.gradEnergy φ + LQGMetric.gradEnergy ψ) / 2 =
      (LQGMetric.pair0 g (LQGMetric.cmTest0 φ) - LQGMetric.gradEnergy φ / 2) +
      (LQGMetric.pair0 g (LQGMetric.cmTest0 ψ) - LQGMetric.gradEnergy ψ / 2) := by
    ring
  rw [he, Real.exp_add]

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
