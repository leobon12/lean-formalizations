import SupercriticalLQGUniqueness.B2.PfeAxioms.RationalScaleSkC

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_positive_subseq_limit_of_eventually_Icc
    (x : ℕ → ℝ) {a b : ℝ} (ha : 0 < a)
    (hbound : ∀ᶠ n in atTop, x n ∈ Icc a b) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Ioi (0 : ℝ), Tendsto (fun n => x (φ n)) atTop (𝓝 (c : ℝ)) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hbound
  let y : ℕ → ℝ := fun n => x (n + N)
  have hy : ∀ n, y n ∈ Icc a b := fun n => hN (n + N) (by omega)
  obtain ⟨c, hc, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hy
  let φ : ℕ → ℕ := fun n => ψ n + N
  have hφ : StrictMono φ := fun i j hij => Nat.add_lt_add_right (hψ hij) N
  refine ⟨φ, hφ, ⟨c, lt_of_lt_of_le ha hc.1⟩, ?_⟩
  simpa only [φ, y, Function.comp_def] using hlim

end SupercriticalLQGUniqueness.B2.PfeAxioms
