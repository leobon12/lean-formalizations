import HigherDimLQGMetric.Limits.StableAdjoin
import Mathlib.Probability.ConditionalProbability

/-! Stable metric convergence under conditioning on a field event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ProbabilityTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Integration under a conditional probability measure is restriction followed
by one fixed scalar multiplication. -/
theorem l6c_integral_cond_field {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistRd d) (A : Set (DistRd d))
    (hh : Measurable h) (hA : MeasurableSet A) (f : Ω → ℝ) :
    ∫ ω, f ω ∂P[|h ⁻¹' A] =
      (P (h ⁻¹' A))⁻¹.toReal *
        ∫ ω, (h ⁻¹' A).indicator f ω ∂P := by
  rw [ProbabilityTheory.cond, integral_smul_measure,
    ← integral_indicator (hA.preimage hh)]
  rfl

/-- Stable convergence persists after conditioning on any positive-probability
event measurable from the fixed field. -/
theorem l6c_stable_cond_field {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hstable : StablyTendstoLU P h X Y)
    (A : Set (DistRd d)) (hA : MeasurableSet A)
    (_hpos : P (h ⁻¹' A) ≠ 0) :
    let PA := P[|h ⁻¹' A]
    StablyTendstoLU PA h X Y := by
  let PA := P[|h ⁻¹' A]
  letI : IsProbabilityMeasure PA := cond_isProbabilityMeasure _hpos
  change StablyTendstoLU PA h X Y
  intro g hg hgb φ hφ hφb
  classical
  let gA : DistRd d → ℝ := fun u => if u ∈ A then g u else 0
  have hgAm : Measurable gA :=
    hg.piecewise hA measurable_const
  have hgAb : ∃ C, ∀ u, |gA u| ≤ C := by
    obtain ⟨C, hC⟩ := hgb
    refine ⟨max C 0, fun u => ?_⟩
    by_cases hu : u ∈ A
    · simpa only [gA, hu, ↓reduceIte] using (hC u).trans (le_max_left _ _)
    · simp only [gA, hu, ↓reduceIte, abs_zero]
      exact le_max_right _ _
  have ht := hstable gA hgAm hgAb φ hφ hφb
  have hrepr (Z : Ω → C(Rd d × Rd d, ℝ)) :
      (∫ ω, g (h ω) * φ (Z ω) ∂PA) =
        (P (h ⁻¹' A))⁻¹.toReal *
          ∫ ω, gA (h ω) * φ (Z ω) ∂P := by
    rw [l6c_integral_cond_field P h A hh hA]
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    by_cases hw : h ω ∈ A <;> simp [gA, hw]
  simpa only [hrepr] using ht.const_mul (P (h ⁻¹' A))⁻¹.toReal

end HigherDimLQGMetric
