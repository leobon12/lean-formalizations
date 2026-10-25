import SupercriticalLQGUniqueness.B2.DG20Lim.RationalUpper
import SupercriticalLQGUniqueness.B2.DG20Lim.AroundLimit

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem RData.across_zero_le_DfromR_of_good_circles (R : RData)
    (Z W : RatCircle) (hZW : Z.center ≠ W.center)
    (U V Uo Vo : ℕ → RatCircle) (Au Av : ℕ → RatAnnulus)
    (hU : ∀ᶠ n in atTop, (U n).Surrounds Z.center)
    (hV : ∀ᶠ n in atTop, (V n).Surrounds W.center)
    (hrU : Tendsto (fun n => ((U n).radius : ℝ)) atTop (𝓝 0))
    (hrV : Tendsto (fun n => ((V n).radius : ℝ)) atTop (𝓝 0))
    (hAu : ∀ᶠ n in atTop,
      (Au n).OppositeSides Z (Uo n) ∧
        (Au n).OppositeSides (V n) (U n))
    (hAv : ∀ᶠ n in atTop,
      (Av n).OppositeSides Z (V n) ∧
        (Av n).OppositeSides W (Vo n))
    (hUo : Tendsto (fun n => R.across Z (Uo n)) atTop (𝓝 0))
    (hVo : Tendsto (fun n => R.across W (Vo n)) atTop (𝓝 0))
    (hAu0 : Tendsto (fun n => R.around (Au n)) atTop (𝓝 0))
    (hAv0 : Tendsto (fun n => R.around (Av n)) atTop (𝓝 0)) :
    R.across Z W ≤ R.DfromR Z.center W.center := by
  have hUV := R.tendsto_across_shrinking hZW U V hU hV hrU hrV
  have hbound : ∀ᶠ n in atTop,
      R.across Z W ≤
        R.across Z (Uo n) + R.across (U n) (V n) + R.around (Au n) +
          R.across W (Vo n) + R.around (Av n) := by
    filter_upwards [hAu, hAv] with n hnAu hnAv
    have h1 := R.around_upper (Au n) Z (Uo n) (V n) (U n)
      hnAu.1 hnAu.2
    have h2 := R.around_upper (Av n) Z (V n) W (Vo n)
      hnAv.1 hnAv.2
    calc
      R.across Z W ≤ R.across Z (V n) + R.across W (Vo n) + R.around (Av n) := h2
      _ ≤ (R.across Z (Uo n) + R.across (V n) (U n) + R.around (Au n)) +
          R.across W (Vo n) + R.around (Av n) := by
        gcongr
      _ = R.across Z (Uo n) + R.across (U n) (V n) + R.around (Au n) +
          R.across W (Vo n) + R.around (Av n) := by
        rw [R.across_symm (V n) (U n)]
  have hsum : Tendsto
      (fun n => R.across Z (Uo n) + R.across (U n) (V n) + R.around (Au n) +
          R.across W (Vo n) + R.around (Av n)) atTop
      (𝓝 (R.DfromR Z.center W.center)) := by
    convert (((hUo.add hUV).add hAu0).add hVo).add hAv0 using 1; simp
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hsum hbound

end SupercriticalLQGUniqueness.B2.DG20Lim
