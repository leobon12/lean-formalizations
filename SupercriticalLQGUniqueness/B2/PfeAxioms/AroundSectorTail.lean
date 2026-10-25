import SupercriticalLQGUniqueness.B2.PfeAxioms.AroundSectorBound

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Strong

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem around_upper_tail_of_sector_upper_tail
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ι → Ω → LSCMetric) (A : ι → EuclideanAnnulus)
    (M : ℝ) (hM : 0 < M) (δ : ℝ≥0∞)
    (hsector : ∀ i k, P {ω | ENNReal.ofReal M <
      (D i ω).internalSetDist (cfgOpens (A i) k : Set ℂ)
        (Subtype.val ⁻¹' cfgSet₁ (A i) k)
        (Subtype.val ⁻¹' cfgSet₂ (A i) k)} ≤ δ) :
    ∀ i, P {ω | (ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M) +
      ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M)) <
        aroundDist (D i ω) (A i)} ≤ δ + δ + δ + δ := by
  intro i
  let a : ℝ≥0∞ := ENNReal.ofReal M
  let b : ℝ≥0∞ := ENNReal.ofReal (2 * M)
  have hab : a < b := by
    change ENNReal.ofReal M < ENNReal.ofReal (2 * M)
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hsub : {ω | b + b + b + b < aroundDist (D i ω) (A i)} ⊆
      ⋃ k : Fin 4, {ω | a < (D i ω).internalSetDist
        (cfgOpens (A i) k : Set ℂ)
        (Subtype.val ⁻¹' cfgSet₁ (A i) k)
        (Subtype.val ⁻¹' cfgSet₂ (A i) k)} := by
    intro ω hω
    by_contra hn
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hn
    have hk : ∀ k : Fin 4, (D i ω).internalSetDist
        (cfgOpens (A i) k : Set ℂ)
        (Subtype.val ⁻¹' cfgSet₁ (A i) k)
        (Subtype.val ⁻¹' cfgSet₂ (A i) k) < b := fun k => (hn k).trans_lt hab
    exact (lt_asymm hω (aroundDist_lt_four_sector_bound (D i ω) (A i) b hk))
  calc
    P {ω | b + b + b + b < aroundDist (D i ω) (A i)}
      ≤ P (⋃ k : Fin 4, {ω | a < (D i ω).internalSetDist
          (cfgOpens (A i) k : Set ℂ)
          (Subtype.val ⁻¹' cfgSet₁ (A i) k)
          (Subtype.val ⁻¹' cfgSet₂ (A i) k)}) := measure_mono hsub
    _ ≤ ∑' k : Fin 4, P {ω | a < (D i ω).internalSetDist
          (cfgOpens (A i) k : Set ℂ)
          (Subtype.val ⁻¹' cfgSet₁ (A i) k)
          (Subtype.val ⁻¹' cfgSet₂ (A i) k)} := measure_iUnion_le _
    _ ≤ ∑' _k : Fin 4, δ := ENNReal.tsum_le_tsum (fun k => hsector i k)
    _ = δ + δ + δ + δ := by simp [tsum_fintype]; ring

end SupercriticalLQGUniqueness.B2.PfeAxioms
