import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPMesh

 







set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_lfpp_mesh_budget {L m r η : ℝ}
    (_hL : 0 ≤ L) (hm : 0 < m) (hr : 0 < r) (hη : 0 < η) :
    ∃ N : ℕ,
      0 < η / (N + 1 : ℝ) ∧
      L / (N + 1 : ℝ) + η / (N + 1 : ℝ) < m * r := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((L + η) / (m * r))
  have ha : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hmr : 0 < m * r := mul_pos hm hr
  refine ⟨N, div_pos hη ha, ?_⟩
  have hN' : L + η < (N : ℝ) * (m * r) :=
    (div_lt_iff₀ hmr).mp hN
  have hsum : L / (N + 1 : ℝ) + η / (N + 1 : ℝ) =
      (L + η) / (N + 1 : ℝ) := by ring
  rw [hsum, div_lt_iff₀ ha]
  nlinarith

theorem lfpp_mesh_total_eq (N : ℕ) {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) :
    (∑ _i ∈ Finset.range (N + 1),
      (ENNReal.ofReal (L / (N + 1 : ℝ)) +
        ENNReal.ofReal (η / (N + 1 : ℝ)))) =
      ENNReal.ofReal (L + η) := by
  have ha : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have hB : 0 ≤ L / (N + 1 : ℝ) := div_nonneg hL ha.le
  have hδ : 0 ≤ η / (N + 1 : ℝ) := div_nonneg hη ha.le
  simp only [Finset.sum_const, Finset.card_range]
  rw [← ENNReal.ofReal_add hB hδ, ← ENNReal.ofReal_nsmul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  field_simp

end SupercriticalLQGUniqueness.B2.PfeAxioms
