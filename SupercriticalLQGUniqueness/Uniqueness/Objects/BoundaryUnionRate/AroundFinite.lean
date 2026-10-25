import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.TailFinite
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Tail




 




set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

def normalizedAroundCost (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (g : LQGMetric.DistC) (s : Set.Ioi (0 : ℝ)) (y : ℂ) : ENNReal :=
  Objects.CorrectedEvent.around (D g) y ((1/2) * s) (1 * s) / Objects.AnnulusTails.nrm ξ Q g s y

theorem ae_normalizedAroundCost_lt_top
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (s : Set.Ioi (0 : ℝ)) (y : ℂ) :
    ∀ᵐ ω ∂P, normalizedAroundCost ξ Q D (h ω) s y < ∞ := by
  obtain ⟨R₀, C, hR₀, hC, htail⟩ :=
    Objects.AnnulusTails.around_upper_tail ξ Q hQ D hD (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) < 1) 1 (by norm_num)
  apply ae_lt_top_of_inverse_tail P
    (fun ω => normalizedAroundCost ξ Q D (h ω) s y) R₀ C hR₀
  intro R hR
  have hNpos (ω : Ω) : 0 < Objects.AnnulusTails.nrm ξ Q (h ω) s y := by
    unfold Objects.AnnulusTails.nrm
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (Real.rpow_pos_of_pos s.2 _) (Real.exp_pos _)
  have hNfinite (ω : Ω) : Objects.AnnulusTails.nrm ξ Q (h ω) s y ≠ ∞ := by
    unfold Objects.AnnulusTails.nrm
    exact ENNReal.ofReal_ne_top
  have hevent :
      {ω | ENNReal.ofReal R < normalizedAroundCost ξ Q D (h ω) s y} =
      {ω | ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q (h ω) s y <
          Objects.CorrectedEvent.around (D (h ω)) y ((1/2) * s) (1 * s)} := by
    ext ω
    change ENNReal.ofReal R <
      Objects.CorrectedEvent.around (D (h ω)) y ((1/2) * s) (1 * s) /
        Objects.AnnulusTails.nrm ξ Q (h ω) s y ↔ _
    exact ENNReal.lt_div_iff_mul_lt (Or.inl (hNpos ω).ne')
      (Or.inl (hNfinite ω))
  rw [hevent]
  convert htail P h hh R hR s y using 1
  rw [Real.rpow_neg_one, div_eq_mul_inv]


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
