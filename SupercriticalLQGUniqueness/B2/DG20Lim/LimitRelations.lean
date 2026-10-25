import SupercriticalLQGUniqueness.B2.DG20Lim.ChainOne

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem chain_lower_of_tendsto
    (C : ℕ → RatCircle → RatCircle → ℝ≥0∞)
    (R : RatCircle → RatCircle → ℝ≥0∞)
    (hC : ∀ O P, Tendsto (fun n => C n O P) atTop (nhds (R O P)))
    (k : ℕ) (O : Fin (k + 1) → RatCircle)
    (hchain : ∀ n, (∑ j : Fin k,
      C n (O ⟨j.val, by omega⟩) (O ⟨j.val + 1, by omega⟩)) ≤
        C n (O ⟨0, by omega⟩) (O ⟨k, by omega⟩)) :
    (∑ j : Fin k,
      R (O ⟨j.val, by omega⟩) (O ⟨j.val + 1, by omega⟩)) ≤
        R (O ⟨0, by omega⟩) (O ⟨k, by omega⟩) := by
  have hsum : Tendsto (fun n => ∑ j : Fin k,
      C n (O ⟨j.val, by omega⟩) (O ⟨j.val + 1, by omega⟩)) atTop
      (nhds (∑ j : Fin k,
        R (O ⟨j.val, by omega⟩) (O ⟨j.val + 1, by omega⟩))) := by
    apply tendsto_finsetSum
    intro j _
    exact hC _ _
  exact le_of_tendsto_of_tendsto hsum (hC _ _)
    (Eventually.of_forall hchain)

 

theorem around_upper_of_tendsto
    (C : ℕ → RatCircle → RatCircle → ℝ≥0∞)
    (B : ℕ → RatAnnulus → ℝ≥0∞)
    (R : RatCircle → RatCircle → ℝ≥0∞)
    (S : RatAnnulus → ℝ≥0∞)
    (hC : ∀ O P, Tendsto (fun n => C n O P) atTop (nhds (R O P)))
    (hB : ∀ A, Tendsto (fun n => B n A) atTop (nhds (S A)))
    (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle)
    (hbound : ∀ n,
      C n O₁ O₂ ≤ C n O₁ O₁' + C n O₂ O₂' + B n A) :
    R O₁ O₂ ≤ R O₁ O₁' + R O₂ O₂' + S A := by
  exact le_of_tendsto_of_tendsto (hC _ _)
    ((hC _ _).add (hC _ _) |>.add (hB _))
    (Eventually.of_forall hbound)

 
theorem across_symm_of_tendsto
    (C : ℕ → RatCircle → RatCircle → ℝ≥0∞)
    (R : RatCircle → RatCircle → ℝ≥0∞)
    (hC : ∀ O P, Tendsto (fun n => C n O P) atTop (nhds (R O P)))
    (hSymm : ∀ n O P, C n O P = C n P O)
    (O P : RatCircle) : R O P = R P O := by
  exact tendsto_nhds_unique (hC O P)
    ((hC P O).congr' (Eventually.of_forall fun n => (hSymm n O P).symm))

 

theorem across_pos_of_tendsto_of_lower
    (C : ℕ → RatCircle → RatCircle → ℝ≥0∞)
    (R : RatCircle → RatCircle → ℝ≥0∞)
    (hC : ∀ O P, Tendsto (fun n => C n O P) atTop (nhds (R O P)))
    (O P : RatCircle) (δ : ℝ≥0∞) (hδ : 0 < δ)
    (hlower : ∀ᶠ n in atTop, δ ≤ C n O P) :
    0 < R O P := by
  have hconst : Tendsto (fun _ : ℕ => δ) atTop (nhds δ) := tendsto_const_nhds
  exact lt_of_lt_of_le hδ
    (le_of_tendsto_of_tendsto hconst (hC O P) hlower)

end SupercriticalLQGUniqueness.B2.DG20Lim
