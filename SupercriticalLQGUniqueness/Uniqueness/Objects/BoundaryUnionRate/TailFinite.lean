import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Tail
import Mathlib.Analysis.SpecialFunctions.Pow.Integral




 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem ae_lt_top_of_upper_tight
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ≥0∞)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
      μ {ω | ENNReal.ofReal M < X ω} ≤ ENNReal.ofReal ε) :
    ∀ᵐ ω ∂μ, X ω < ∞ := by
  have hzero : μ {ω | X ω = ∞} = 0 := by
    apply le_antisymm ?_ (bot_le)
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨M, hM, hbound⟩ := htight ε hε
    have hsub : {ω | X ω = ∞} ⊆ {ω | ENNReal.ofReal M < X ω} := by
      intro ω hω
      change X ω = ∞ at hω
      change ENNReal.ofReal M < X ω
      rw [hω]
      exact ENNReal.ofReal_lt_top
    calc
      μ {ω | X ω = ∞} ≤ μ {ω | ENNReal.ofReal M < X ω} := measure_mono hsub
      _ ≤ ENNReal.ofReal ε := hbound
      _ = 0 + ε := by simp
  rw [ae_iff]
  simpa only [not_lt, top_le_iff] using hzero

theorem ae_lt_top_of_inverse_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ≥0∞) (R₀ C : ℝ) (hR₀ : 1 ≤ R₀)
    (htail : ∀ R : ℝ, R₀ ≤ R →
      μ {ω | ENNReal.ofReal R < X ω} ≤ ENNReal.ofReal (C / R)) :
    ∀ᵐ ω ∂μ, X ω < ∞ := by
  apply ae_lt_top_of_upper_tight μ X
  intro ε hε
  let M : ℝ := max R₀ (C / ε)
  have hM₀ : 0 < M := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hR₀) (le_max_left ..)
  have hM : R₀ ≤ M := le_max_left ..
  have hCε : C ≤ ε * M := by
    have h := le_max_right R₀ (C / ε)
    rw [div_le_iff₀ hε] at h
    nlinarith
  have hbound : C / M ≤ ε := (div_le_iff₀ hM₀).2 (by nlinarith)
  refine ⟨M, hM₀, ?_⟩
  calc
    μ {ω | ENNReal.ofReal M < X ω} ≤ ENNReal.ofReal (C / M) := htail M hM
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hbound


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
