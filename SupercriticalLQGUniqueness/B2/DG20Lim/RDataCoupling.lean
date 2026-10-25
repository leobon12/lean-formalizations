import SupercriticalLQGUniqueness.B2.DG20Lim.RDataPositiveCoords

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_has_rdata_of_coord_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → RatCoords) (y : Ω → RatCoords)
    (hConv : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (y ω)))
    (hSymm : ∀ᵐ ω ∂P, ∀ n O Pcircle,
      (Y n ω).1 (O, Pcircle) = (Y n ω).1 (Pcircle, O))
    (hChain : ∀ᵐ ω ∂P,
      ∀ n (k : ℕ) (O : Fin (k + 1) → RatCircle),
        (∀ i j : Fin (k + 1), i ≠ j →
          Disjoint (O i).toSet (O j).toSet) →
        (∀ j : ℕ, (hj : 0 < j) → (hk : j < k) →
          Disconnects (O ⟨j, by omega⟩).toSet
            (O ⟨j - 1, by omega⟩).toSet
            (O ⟨j + 1, by omega⟩).toSet) →
        (∑ j : Fin k,
          (Y n ω).1 (O ⟨j.val, by omega⟩,
            O ⟨j.val + 1, by omega⟩)) ≤
          (Y n ω).1 (O ⟨0, by omega⟩, O ⟨k, by omega⟩))
    (hAround : ∀ᵐ ω ∂P,
      ∀ n (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle),
        A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
        (Y n ω).1 (O₁, O₂) ≤ (Y n ω).1 (O₁, O₁') +
          (Y n ω).1 (O₂, O₂') + (Y n ω).2 A)
    (hPos : ∀ᵐ ω ∂P, ∀ O Pcircle,
      Disjoint O.toSet Pcircle.toSet →
        0 < (y ω).1 (O, Pcircle)) :
    ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Pcircle => (y ω).1 (O, Pcircle)) ∧
      R.around = (y ω).2 := by
  filter_upwards [hSymm, hChain, hAround, hPos] with ω hs hc ha hp
  exact RatCoords.has_rdata_of_samplewise_bounds_of_pos
    (fun n => Y n ω) (y ω) (hConv ω) hs hc ha hp

end SupercriticalLQGUniqueness.B2.DG20Lim
