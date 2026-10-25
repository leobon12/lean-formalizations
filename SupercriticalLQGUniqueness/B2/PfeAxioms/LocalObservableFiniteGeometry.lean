import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNormalizedContinuous
import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsGeometry0
import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPLength
import SupercriticalLQGUniqueness.B2.PfeLocal.OpenInternalBridge

 

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem normalizedLFPPMetric_small_euclidean
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    ∀ u : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ,
          (PfeWeyl.normalizedLFPPMetric ξ a φ).1 (u, v) <
            ENNReal.ofReal η → dist u v < δ := by
  intro u δ hδ
  obtain ⟨η₀, hη₀, hsmall⟩ :=
    LQGMetric.LFPP.lfppDReal_euclidean_of_small
      (ξ := ξ) (φ := (φ : ℂ → ℝ)) φ.continuous u δ hδ
  let c : ℝ := (a : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr a.property
  refine ⟨c * η₀, mul_pos hc hη₀, ?_⟩
  intro v hv
  have hfin := LQGMetric.LFPP.lfppD_ne_top
    (ξ := ξ) φ.continuous u v
  have hreal : c * LQGMetric.LFPP.lfppDReal ξ φ (u, v) < c * η₀ := by
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc hη₀)).mp
    convert hv using 1
    rw [PfeWeyl.normalizedLFPPMetric_apply,
      B2.LscTop.lfppDistance_eq_lfppD,
      ← ENNReal.ofReal_toReal hfin,
      ← ENNReal.ofReal_mul hc.le]
    rfl
  have hdist : LQGMetric.LFPP.lfppDReal ξ φ (u, v) < η₀ :=
    lt_of_mul_lt_mul_left hreal hc.le
  simpa only [dist_eq_norm] using hsmall v hdist

theorem finitePathsEuclideanContinuous_normalizedLFPPMetric
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    FinitePathsEuclideanContinuous
      (PfeWeyl.normalizedLFPPMetric ξ a φ) :=
  finitePathsEuclideanContinuous_of_control _
    (normalizedLFPPMetric_small_euclidean ξ a φ)

theorem continuous_euclidForget_normalizedLFPPMetric
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    Continuous
      (PfeWeyl.euclidForget
        (PfeWeyl.normalizedLFPPMetric ξ a φ)) := by
  exact B2.PfeLocal.continuous_euclidForget_of_small_metric _
    (normalizedLFPPMetric_small_euclidean ξ a φ)

theorem normalizedLFPPMetric_finite_geometry
    (ξ : ℝ) (a : ℕ → Ioi (0 : ℝ))
    (φ : ℕ → C(ℂ, ℝ)) :
    (∀ n, (PfeWeyl.normalizedLFPPMetric ξ (a n) (φ n)).IsLengthSpace) ∧
    (∀ n, FinitePathsEuclideanContinuous
      (PfeWeyl.normalizedLFPPMetric ξ (a n) (φ n))) ∧
    (∀ n, Continuous
      (PfeWeyl.euclidForget
        (PfeWeyl.normalizedLFPPMetric ξ (a n) (φ n)))) := by
  exact ⟨fun n => PfeWeyl.isLengthSpace_normalizedLFPPMetric ξ (a n) (φ n),
    fun n => finitePathsEuclideanContinuous_normalizedLFPPMetric ξ (a n) (φ n),
    fun n => continuous_euclidForget_normalizedLFPPMetric ξ (a n) (φ n)⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
