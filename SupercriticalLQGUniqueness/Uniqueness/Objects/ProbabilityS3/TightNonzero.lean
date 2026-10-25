import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.ExactCost




 


set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem ae_pos_lt_top_of_twoSidedTight
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ι → Ω → ℝ≥0∞) (hX : IsTwoSidedTight μ X) (i : ι) :
    ∀ᵐ ω ∂μ, 0 < X i ω ∧ X i ω < ⊤ := by
  have hz : μ {ω | X i ω = 0} = 0 := by
    apply le_antisymm _ bot_le
    refine ENNReal.le_of_forall_pos_le_add (b := 0) ?_
    intro ε hε _
    obtain ⟨M, hM, hMtail⟩ := hX.2 (ε : ℝ) hε
    have hsmall := (hMtail i).2
    have hminv : 0 < ENNReal.ofReal M⁻¹ :=
      ENNReal.ofReal_pos.mpr (inv_pos.mpr hM)
    calc
      μ {ω | X i ω = 0} ≤ μ {ω | X i ω < ENNReal.ofReal M⁻¹} := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [hω]
        exact hminv
      _ ≤ ENNReal.ofReal (ε : ℝ) := hsmall
      _ = 0 + (ε : ℝ≥0∞) := by simp
  have ht : μ {ω | X i ω = ⊤} = 0 := by
    apply le_antisymm _ bot_le
    refine ENNReal.le_of_forall_pos_le_add (b := 0) ?_
    intro ε hε _
    obtain ⟨M, hM, hMtail⟩ := hX.2 (ε : ℝ) hε
    have hlarge := (hMtail i).1
    have hMtop : ENNReal.ofReal M < ⊤ := ENNReal.ofReal_lt_top
    calc
      μ {ω | X i ω = ⊤} ≤ μ {ω | ENNReal.ofReal M < X i ω} := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        rw [hω]
        exact hMtop
      _ ≤ ENNReal.ofReal (ε : ℝ) := hlarge
      _ = 0 + (ε : ℝ≥0∞) := by simp
  have hzero : ∀ᵐ ω ∂μ, X i ω ≠ 0 := by
    rw [ae_iff]
    simpa using hz
  have htop : ∀ᵐ ω ∂μ, X i ω ≠ ⊤ := by
    rw [ae_iff]
    simpa using ht
  filter_upwards [hzero, htop] with ω hw0 hwtop
  exact ⟨pos_iff_ne_zero.mpr hw0, lt_top_iff_ne_top.mpr hwtop⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
