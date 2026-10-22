import HigherDimLQGMetric.Amplify.Independent

/-! A finite independent-trial estimate with one union bound over boxes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- If every trial has failure probability at most `q`, the probability of a
box with no successful trial is at most `M q^N`. -/
theorem amplify_box_fail_le {M N : ℕ}
    (m : Fin M → Fin N → MeasurableSpace Ω)
    (E : Fin M → Fin N → Set Ω)
    (hm : ∀ i, iIndep (m i) P)
    (hE : ∀ i k, AEEventIn P (m i k) (E i k))
    {q : ℝ≥0∞} (hq : ∀ i k, P ((E i k)ᶜ) ≤ q) :
    P {ω | ∃ i : Fin M, ∀ k : Fin N, ω ∉ E i k} ≤
      (M : ℝ≥0∞) * q ^ N := by
  have hi (i : Fin M) : P {ω | ∀ k : Fin N, ω ∉ E i k} ≤ q ^ N := by
    have h := amplify_all_fail_le_pow (P := P) (E := E i) (hm i) Finset.univ
      (fun k _ => hE i k) (fun k _ => hq i k)
    have heq : {ω | ∀ k : Fin N, ω ∉ E i k} =
        ⋂ k ∈ (Finset.univ : Finset (Fin N)), (E i k)ᶜ := by
      ext ω
      simp
    rw [heq]
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have hunion := measure_iUnion_fintype_le P
    (fun i : Fin M => {ω | ∀ k : Fin N, ω ∉ E i k})
  have hsum : (∑ i : Fin M, P {ω | ∀ k : Fin N, ω ∉ E i k}) ≤
      ∑ _i : Fin M, q ^ N :=
    Finset.sum_le_sum fun i _ => hi i
  calc
    P {ω | ∃ i : Fin M, ∀ k : Fin N, ω ∉ E i k} =
        P (⋃ i : Fin M, {ω | ∀ k : Fin N, ω ∉ E i k}) := by
          congr 1
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    _ ≤ ∑ i : Fin M, P {ω | ∀ k : Fin N, ω ∉ E i k} := hunion
    _ ≤ ∑ _i : Fin M, q ^ N := hsum
    _ = (M : ℝ≥0∞) * q ^ N := by simp

end HigherDimLQGMetric
