import HigherDimLQGMetric.DGZ.NondegEventuallyPair

/-! A uniform bound on eventual measurable events also bounds the initiating event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

theorem nd_measure_le_of_ae_eventually
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (Z : Set X) (F : ℕ → Set X) (M : ℝ≥0∞)
    (hev : ∀ᵐ x ∂μ, x ∈ Z → ∀ᶠ j : ℕ in atTop, x ∈ F j)
    (hF : ∀ j, μ (F j) ≤ M) : μ Z ≤ M := by
  let B (n : ℕ) : Set X := ⋂ j : {j : ℕ // n ≤ j}, F j.1
  have hBmono : Monotone B := by
    intro n m hnm x hx
    apply Set.mem_iInter.2
    intro j
    exact Set.mem_iInter.mp hx ⟨j.1, hnm.trans j.2⟩
  have hZ : μ Z ≤ μ (⋃ n, B n) := by
    apply measure_mono_ae
    filter_upwards [hev] with x hx hxZ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hx hxZ)
    exact Set.mem_iUnion.2 ⟨N, Set.mem_iInter.2 fun j => hN j.1 j.2⟩
  calc
    μ Z ≤ μ (⋃ n, B n) := hZ
    _ = ⨆ n, μ (B n) := hBmono.measure_iUnion
    _ ≤ M := iSup_le fun n => (measure_mono
      (show B n ⊆ F n by
        intro x hx
        exact Set.mem_iInter.mp hx ⟨n, le_rfl⟩)).trans (hF n)

end HigherDimLQGMetric.DGZ
