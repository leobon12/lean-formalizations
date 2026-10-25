import SupercriticalLQGUniqueness.B2.DG20Lim.RDataFromCoords

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatCoords.has_rdata_of_samplewise_bounds_of_pos
    (Y : ℕ → RatCoords) (y : RatCoords)
    (hY : Tendsto Y atTop (𝓝 y))
    (hSymm : ∀ n O P, (Y n).1 (O, P) = (Y n).1 (P, O))
    (hChain : ∀ n (k : ℕ) (O : Fin (k + 1) → RatCircle),
      (∀ i j : Fin (k + 1), i ≠ j →
        Disjoint (O i).toSet (O j).toSet) →
      (∀ j : ℕ, (hj : 0 < j) → (hk : j < k) →
        Disconnects (O ⟨j, by omega⟩).toSet
          (O ⟨j - 1, by omega⟩).toSet
          (O ⟨j + 1, by omega⟩).toSet) →
      (∑ j : Fin k,
        (Y n).1 (O ⟨j.val, by omega⟩,
          O ⟨j.val + 1, by omega⟩)) ≤
        (Y n).1 (O ⟨0, by omega⟩, O ⟨k, by omega⟩))
    (hAround : ∀ n (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle),
      A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
      (Y n).1 (O₁, O₂) ≤ (Y n).1 (O₁, O₁') +
        (Y n).1 (O₂, O₂') + (Y n).2 A)
    (hPos : ∀ O P, Disjoint O.toSet P.toSet →
      0 < y.1 (O, P)) :
    ∃ R : RData, R.across = (fun O P => y.1 (O, P)) ∧
      R.around = y.2 := by
  apply RatCoords.has_rdata_of_samplewise_bounds Y y hY hSymm hChain hAround
  intro O P hdisj
  obtain ⟨δ, hδ, hδy⟩ := exists_between (hPos O P hdisj)
  have hcoord : Tendsto (fun n => (Y n).1 (O, P)) atTop
      (𝓝 (y.1 (O, P))) :=
    (((continuous_apply (O, P)).comp continuous_fst).tendsto y).comp hY
  refine ⟨δ, hδ, ?_⟩
  exact (hcoord.eventually (isOpen_Ioi.mem_nhds hδy)).mono
    (fun n hn => hn.le)

end SupercriticalLQGUniqueness.B2.DG20Lim
