import SupercriticalLQGUniqueness.B2.WeakStrong.Constant
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.Gapc2

 












set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC addConst IsGFFPlusCont)

namespace SupercriticalLQGUniqueness.B2.WeakStrong

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

 
theorem scaling_of_weak (hQ : IsLFPPExponent ξ Q) (hD : IsWeakLQGMetric ξ Q D) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P → ∀ (r : Set.Ioi (0 : ℝ)) (z : ℂ), ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (D (h ω)).1 ((r : ℝ) • u + z, (r : ℝ) • v + z) =
          (D (addConst (scaleTranslateDist r z (h ω)) (Q * Real.log (r : ℝ)))).1 (u, v) := by
  intro Ω _ P _ h hh r z
  obtain ⟨C, hC0, hC⟩ := exists_dilConst hQ hD r
  obtain ⟨k, -, hk, -, -, -⟩ := Uniqueness.TwoScale.GapChecks.exists_normalized_decomposition hh
  have h1 : C = 1 := const_eq_one_of_dilConst hD hC0 hC hk
  filter_upwards [hD.2.2.2.2.1 P h hh z, hC P _ (isGFFPlusCont_translate hh z)] with ω hT hR u v
  have e := hR ((r : ℝ) • u) ((r : ℝ) • v)
  rw [h1, ENNReal.ofReal_one, one_mul, dilMetric_apply, inv_smul_smul₀ (ne_of_gt r.2),
    inv_smul_smul₀ (ne_of_gt r.2)] at e
  rw [← hT, addConst_scaleTranslate_eq]
  exact e.symm

end SupercriticalLQGUniqueness.B2.WeakStrong
