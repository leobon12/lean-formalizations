import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLengthTransfer

 



set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

def RData.of_coord_tendsto
    (C : ℕ → RatCircle → RatCircle → ℝ≥0∞)
    (B : ℕ → RatAnnulus → ℝ≥0∞)
    (R : RatCircle → RatCircle → ℝ≥0∞)
    (S : RatAnnulus → ℝ≥0∞)
    (hC : ∀ O P, Tendsto (fun n => C n O P) atTop (nhds (R O P)))
    (hB : ∀ A, Tendsto (fun n => B n A) atTop (nhds (S A)))
    (hSymm : ∀ n O P, C n O P = C n P O)
    (hChain : ∀ n (k : ℕ) (O : Fin (k + 1) → RatCircle),
      (∀ i j : Fin (k + 1), i ≠ j →
        Disjoint (O i).toSet (O j).toSet) →
      (∀ j : ℕ, (hj : 0 < j) → (hk : j < k) →
        Disconnects (O ⟨j, by omega⟩).toSet
          (O ⟨j - 1, by omega⟩).toSet
          (O ⟨j + 1, by omega⟩).toSet) →
      (∑ j : Fin k,
        C n (O ⟨j.val, by omega⟩) (O ⟨j.val + 1, by omega⟩)) ≤
        C n (O ⟨0, by omega⟩) (O ⟨k, by omega⟩))
    (hAround : ∀ n (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle),
      A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
      C n O₁ O₂ ≤ C n O₁ O₁' + C n O₂ O₂' + B n A)
    (hPos : ∀ O P, Disjoint O.toSet P.toSet →
      ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ᶠ n in atTop, δ ≤ C n O P) : RData where
  across := R
  around := S
  across_symm := across_symm_of_tendsto C R hC hSymm
  chain_lower := by
    intro k O hdisj hsep
    exact chain_lower_of_tendsto C R hC k O
      (fun n => hChain n k O hdisj hsep)
  around_upper := by
    intro A O₁ O₁' O₂ O₂' h₁ h₂
    exact around_upper_of_tendsto C B R S hC hB A O₁ O₁' O₂ O₂'
      (fun n => hAround n A O₁ O₁' O₂ O₂' h₁ h₂)
  across_pos := by
    intro O P hdisj
    obtain ⟨δ, hδ, hLower⟩ := hPos O P hdisj
    exact across_pos_of_tendsto_of_lower C R hC O P δ hδ hLower

 
theorem RatCoords.has_rdata_of_samplewise_bounds
    (Y : ℕ → RatCoords) (y : RatCoords)
    (hY : Tendsto Y atTop (nhds y))
    (hSymm : ∀ n O P, (Y n).1 (O, P) = (Y n).1 (P, O))
    (hChain : ∀ n (k : ℕ) (O : Fin (k + 1) → RatCircle),
      (∀ i j : Fin (k + 1), i ≠ j →
        Disjoint (O i).toSet (O j).toSet) →
      (∀ j : ℕ, (hj : 0 < j) → (hk : j < k) →
        Disconnects (O ⟨j, by omega⟩).toSet
          (O ⟨j - 1, by omega⟩).toSet
          (O ⟨j + 1, by omega⟩).toSet) →
      (∑ j : Fin k,
        (Y n).1 (O ⟨j.val, by omega⟩, O ⟨j.val + 1, by omega⟩)) ≤
        (Y n).1 (O ⟨0, by omega⟩, O ⟨k, by omega⟩))
    (hAround : ∀ n (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle),
      A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
      (Y n).1 (O₁, O₂) ≤ (Y n).1 (O₁, O₁') +
        (Y n).1 (O₂, O₂') + (Y n).2 A)
    (hPos : ∀ O P, Disjoint O.toSet P.toSet →
      ∃ δ : ℝ≥0∞, 0 < δ ∧
        ∀ᶠ n in atTop, δ ≤ (Y n).1 (O, P)) :
    ∃ R : RData, R.across = (fun O P => y.1 (O, P)) ∧
      R.around = y.2 := by
  let R := RData.of_coord_tendsto
    (fun n O P => (Y n).1 (O, P)) (fun n A => (Y n).2 A)
    (fun O P => y.1 (O, P)) y.2
    (fun O P => ((continuous_apply (O, P)).comp continuous_fst).tendsto y |>.comp hY)
    (fun A => ((continuous_apply A).comp continuous_snd).tendsto y |>.comp hY)
    hSymm hChain hAround hPos
  exact ⟨R, rfl, rfl⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
