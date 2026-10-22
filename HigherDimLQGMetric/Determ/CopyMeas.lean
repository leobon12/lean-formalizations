import HigherDimLQGMetric.Determ.L53
import HigherDimLQGMetric.Determ.CopyBound
import LQGMetric.Papers.LM.T1_7V11

/-! Measurable cores and dense-pair tests for conditional metric copies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

/-- Every almost-sure event contains a measurable almost-sure event. -/
theorem determ_measurable_ae_subset {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : ∀ᵐ x ∂μ, x ∈ S) :
    ∃ M : Set α, MeasurableSet M ∧ M ⊆ S ∧ ∀ᵐ x ∂μ, x ∈ M := by
  obtain ⟨N, hSN, hNm, hN0⟩ :=
    exists_measurable_superset_of_null (ae_iff.1 hS)
  refine ⟨Nᶜ, hNm.compl, ?_, measure_eq_zero_iff_ae_notMem.1 hN0⟩
  intro x hx
  by_contra hnot
  exact hx (hSN hnot)

theorem determ_le_of_dense {d : ℕ} {D D' : ContMetric d} {c : ℝ}
    (h : ∀ n, D'.1 (TopologicalSpace.denseSeq (Rd d × Rd d) n) ≤
      c * D.1 (TopologicalSpace.denseSeq (Rd d × Rd d) n)) :
    ∀ x y : Rd d, D'.1 (x, y) ≤ c * D.1 (x, y) := by
  have hcl : IsClosed {p : Rd d × Rd d | D'.1 p ≤ c * D.1 p} :=
    isClosed_le D'.1.continuous (continuous_const.mul D.1.continuous)
  have hsub := closure_minimal (s := range (TopologicalSpace.denseSeq (Rd d × Rd d)))
    (by rintro _ ⟨n, rfl⟩; exact h n) hcl
  rw [(TopologicalSpace.denseRange_denseSeq (Rd d × Rd d)).closure_range] at hsub
  exact fun x y => hsub (mem_univ (x, y))

end HigherDimLQGMetric
