import SupercriticalLQGUniqueness.B2.DG20Lim.GoodCircleCoupled

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatCircle.SurroundsCircle.trans {A B C : RatCircle}
    (hAB : A.SurroundsCircle B) (hBC : B.SurroundsCircle C) :
    A.SurroundsCircle C := by
  refine ⟨hAB.1, ?_⟩
  exact hBC.2.trans (B.openDisk_subset_closedDisk.trans hAB.2)

theorem nested_annulus_inner_surrounds_later_outer
    (B : ℕ → RatAnnulus)
    (hnest : ∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer)
    {i j : ℕ} (hij : i < j) :
    (B i).inner.SurroundsCircle (B j).outer := by
  have hstep (i d : ℕ) :
      (B i).inner.SurroundsCircle (B (i + 1 + d)).outer := by
    induction d with
    | zero => simpa using hnest i
    | succ d ih =>
        have hmid : (B i).inner.SurroundsCircle (B (i + 1 + d)).inner :=
          ih.trans (B (i + 1 + d)).nested
        have hnext := hnest (i + 1 + d)
        convert hmid.trans hnext using 1 <;> congr 1 <;> omega
  have heq : i + 1 + (j - i - 1) = j := by omega
  simpa only [heq] using hstep i (j - i - 1)

end SupercriticalLQGUniqueness.B2.DG20Lim
