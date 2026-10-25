import SupercriticalLQGUniqueness.B2.DG20Lim.NestedAnnulusDisjoint

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem nested_annulus_outer_surrounds_later_inner
    (B : ℕ → RatAnnulus)
    (hnest : ∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer)
    (n : ℕ) :
    (B 0).outer.SurroundsCircle (B n).inner := by
  cases n with
  | zero => exact (B 0).nested
  | succ n =>
      have h := nested_annulus_inner_surrounds_later_outer B hnest
        (show 0 < n + 1 by omega)
      exact (B 0).nested.trans (h.trans (B (n + 1)).nested)

end SupercriticalLQGUniqueness.B2.DG20Lim
