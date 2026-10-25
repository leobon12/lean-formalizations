import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.AroundMeas




 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem normalizedAroundCost_upper_tail
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (q : ℝ) (hq : 0 < q) :
    ∃ R₀ C : ℝ, 1 ≤ R₀ ∧ 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ R : ℝ, R₀ ≤ R → ∀ (s : Set.Ioi (0 : ℝ)) (y : ℂ),
          P {ω | ENNReal.ofReal R < normalizedAroundCost ξ Q D (h ω) s y} ≤
            ENNReal.ofReal (C * R ^ (-q)) := by
  obtain ⟨R₀, C, hR₀, hC, htail⟩ :=
    Objects.AnnulusTails.around_upper_tail ξ Q hQ D hD (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) < 1) q hq
  refine ⟨R₀, C, hR₀, hC, ?_⟩
  intro Ω _ P _ h hh R hR s y
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
  exact htail P h hh R hR s y


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
