import HigherDimLQGContinuity.Improve.Union

/-!
# Outer-measure union over net pairs and deterministic catalogues
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory

theorem q11_pair_catalogue_probability {Ω X Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Finset X) (C : Finset Z)
    (sep : X → X → Prop) (hdiag : ∀ x, ¬ sep x x)
    (B : X → X → Z → Set Ω)
    {p q : ℝ}
    (hB : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → ∀ z ∈ C,
      μ (B x y z) ≤ ENNReal.ofReal p)
    (hcount : ((N.card * N.card * C.card : ℕ) : ℝ) * p ≤ q) :
    μ (⋃ x ∈ N, ⋃ y ∈ N, ⋃ z ∈ C,
      {ω | sep x y ∧ ω ∈ B x y z}) ≤
      ENNReal.ofReal q := by
  classical
  let E : X → X → Z → Set Ω := fun x y z =>
    {ω | sep x y ∧ ω ∈ B x y z}
  have hE : ∀ x ∈ N, ∀ y ∈ N, ∀ z ∈ C,
      μ (E x y z) ≤ ENNReal.ofReal p := by
    intro x hx y hy z hz
    by_cases hxy : x = y
    · subst y
      have hempty : E x x z = ∅ := by
        ext ω
        simp [E, hdiag x]
      rw [hempty, measure_empty]
      exact bot_le
    · exact (measure_mono (by intro ω hω; exact hω.2)).trans
        (hB x hx y hy hxy z hz)
  have hsum := q11_pair_catalogue_union_bound μ N N C E (ENNReal.ofReal p) hE
  have hmult : (N.card * N.card * C.card : ℕ) • ENNReal.ofReal p =
      ENNReal.ofReal (((N.card * N.card * C.card : ℕ) : ℝ) * p) := by
    rw [nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (N.card * N.card * C.card : ℕ))]
  calc
    μ (⋃ x ∈ N, ⋃ y ∈ N, ⋃ z ∈ C,
      {ω | sep x y ∧ ω ∈ B x y z})
        ≤ (N.card * N.card * C.card : ℕ) • ENNReal.ofReal p := hsum
    _ = ENNReal.ofReal (((N.card * N.card * C.card : ℕ) : ℝ) * p) := hmult
    _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hcount

end HigherDimLQGContinuity
