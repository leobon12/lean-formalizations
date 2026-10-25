import SupercriticalLQGUniqueness.B2.DG20Lim.LargeCircleGap

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_euclidean_subseq_of_eventually_closedDisk
    (x : ℕ → ℂ) (P : RatCircle)
    (hx : ∀ᶠ n in atTop, x n ∈ P.closedDisk) :
    ∃ (w : ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 w) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx
  have htail : ∀ n, x (n + N) ∈ P.closedDisk := by
    intro n
    exact hN (n + N) (Nat.le_add_left N n)
  obtain ⟨w, _, ψ, hψ, hconv⟩ :=
    (isCompact_closedBall P.center (P.radius : ℝ)).tendsto_subseq htail
  refine ⟨w, fun n => ψ n + N, ?_, ?_⟩
  · intro i j hij
    exact Nat.add_lt_add_right (hψ hij) N
  · simpa only [Function.comp_def] using hconv

end SupercriticalLQGUniqueness.B2.DG20Lim
