import SupercriticalLQGUniqueness.B2.DG20Lim.ChainOne

 






set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem RData.triangle_of_vanishing_around (R : RData)
    {x y z : ℂ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (Ox Oy Oz : ℕ → RatCircle) (A : ℕ → RatAnnulus)
    (hOx : ∀ᶠ n in atTop, (Ox n).Surrounds x)
    (hOy : ∀ᶠ n in atTop, (Oy n).Surrounds y)
    (hOz : ∀ᶠ n in atTop, (Oz n).Surrounds z)
    (hrx : Tendsto (fun n => ((Ox n).radius : ℝ)) atTop (nhds 0))
    (hry : Tendsto (fun n => ((Oy n).radius : ℝ)) atTop (nhds 0))
    (hrz : Tendsto (fun n => ((Oz n).radius : ℝ)) atTop (nhds 0))
    (hAx : ∀ᶠ n in atTop, (A n).OppositeSides (Ox n) (Oy n))
    (hAz : ∀ᶠ n in atTop, (A n).OppositeSides (Oz n) (Oy n))
    (hAround : Tendsto (fun n => R.around (A n)) atTop (nhds 0)) :
    R.DfromR x z ≤ R.DfromR x y + R.DfromR y z := by
  have hL := R.tendsto_across_shrinking hxz Ox Oz hOx hOz hrx hrz
  have hRxy := R.tendsto_across_shrinking hxy Ox Oy hOx hOy hrx hry
  have hRzy := R.tendsto_across_shrinking (Ne.symm hyz) Oz Oy hOz hOy hrz hry
  have hineq : ∀ᶠ n in atTop,
      R.across (Ox n) (Oz n) ≤
        R.across (Ox n) (Oy n) + R.across (Oz n) (Oy n) +
          R.around (A n) := by
    filter_upwards [hAx, hAz] with n hnAx hnAz
    exact R.around_upper (A n) (Ox n) (Oy n) (Oz n) (Oy n) hnAx hnAz
  have hsum : Tendsto
      (fun n => R.across (Ox n) (Oy n) + R.across (Oz n) (Oy n) +
        R.around (A n)) atTop
      (nhds (R.DfromR x y + R.DfromR z y + 0)) :=
    (hRxy.add hRzy).add hAround
  have hbound := le_of_tendsto_of_tendsto hL hsum hineq
  simpa only [add_zero, R.DfromR_symm z y] using hbound

end SupercriticalLQGUniqueness.B2.DG20Lim
