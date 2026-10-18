import BouRabeeGwynne.Section4UniformExitTopology
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Uniform test-function estimates imply uniform Lévy–Prokhorov estimates when the comparison
measures are all carried by one fixed compact set. Via Prokhorov compactness (mathlib) the set of
probability measures carried by a compact set is a compact (metrizable) parameter space, so BRG's
`uniform_levyProkhorovDist_of_uniform_test_error` applies with the identity kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction NNReal

namespace BouRabeeGwynne.MeshRates

/-- Probability measures on `Euc d` carried by a compact set form a compact set. -/
theorem isCompact_probabilityMeasure_carried {d : ℕ} {X : Set (Euc d)} (hX : IsCompact X) :
    IsCompact {m : ProbabilityMeasure (Euc d) | ∀ _ : ℕ, m Xᶜ ≤ (0 : ℝ≥0)} :=
  isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le (u := fun _ => 0)
    tendsto_const_nhds (fun _ => hX) (Or.inr fun _ _ _ => le_rfl)

/-- Uniform bounded-continuous test errors against measures carried by a fixed compact set give
uniform Lévy–Prokhorov errors. -/
theorem uniform_levyProkhorovDist_of_uniform_test_error_carried {d : ℕ} {X : Set (Euc d)}
    (hX : IsCompact X) (V : ℕ → Type*)
    (μ ν : ∀ n, V n → ProbabilityMeasure (Euc d)) (hν : ∀ n v, ν n v Xᶜ = 0)
    (htest : ∀ f : Euc d →ᵇ ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ v : V n, |(∫ x, f x ∂(μ n v : Measure (Euc d))) -
        ∫ x, f x ∂(ν n v : Measure (Euc d))| < η) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V n,
      levyProkhorovDist (μ n v : Measure (Euc d)) (ν n v : Measure (Euc d)) < ε := by
  let S := {m : ProbabilityMeasure (Euc d) | ∀ _ : ℕ, m Xᶜ ≤ (0 : ℝ≥0)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_probabilityMeasure_carried hX)
  let : PseudoMetricSpace S := TopologicalSpace.pseudoMetrizableSpacePseudoMetric S
  have := uniform_levyProkhorovDist_of_uniform_test_error V
    (fun n v => (⟨ν n v, fun _ => (hν n v).le⟩ : S)) μ (fun m : S => (m : ProbabilityMeasure (Euc d)))
    continuous_subtype_val htest
  exact this

end BouRabeeGwynne.MeshRates
