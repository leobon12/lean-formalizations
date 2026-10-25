import SupercriticalLQGUniqueness.B2.DG20Lim.NestedAnnulusOrder

 

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem nested_annulus_disjoint
    (B : ℕ → RatAnnulus)
    (hnest : ∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer)
    {i j : ℕ} (hij : i < j) :
    Disjoint (B i).toSet (B j).toSet := by
  have h := nested_annulus_inner_surrounds_later_outer B hnest hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hzi' : z ∉ (B i).inner.openDisk := hzi.2
  have hzj' : z ∈ (B j).outer.closedDisk := hzj.1
  exact hzi' (h.2 hzj')

end SupercriticalLQGUniqueness.B2.DG20Lim
