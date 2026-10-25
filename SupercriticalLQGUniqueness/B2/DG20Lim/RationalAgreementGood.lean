import SupercriticalLQGUniqueness.B2.DG20Lim.NestedRationalOpposite
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalUpper

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.across_zero_eq_DfromR_of_nested_good
    (R : RData) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (Z W : RatCircle) (hZ : Z.radius = 0) (hW : W.radius = 0)
    (hZW : Z.center ≠ W.center)
    (hGood : ∀ y : ℂ, ∃ B : ℕ → RatAnnulus,
      (∀ n, (B n).inner.Surrounds y ∧
        R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
      (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
      Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0))
    (hZvanish : ∀ O : ℕ → RatCircle,
      (∀ᶠ n in atTop, (O n).Surrounds Z.center) →
      Tendsto (fun n => ((O n).radius : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n => R.across Z (O n)) atTop (𝓝 0))
    (hWvanish : ∀ O : ℕ → RatCircle,
      (∀ᶠ n in atTop, (O n).Surrounds W.center) →
      Tendsto (fun n => ((O n).radius : ℝ)) atTop (𝓝 0) →
      Tendsto (fun n => R.across W (O n)) atTop (𝓝 0)) :
    R.across Z W = R.DfromR Z.center W.center := by
  have hlow := R.DfromR_le_across_zero Z W hZ hW
  by_cases htop : R.DfromR Z.center W.center = ∞
  · exact le_antisymm (by rw [htop]; exact le_top) hlow
  obtain ⟨Bz, hzGood, hnz, hrz⟩ := hGood Z.center
  obtain ⟨Bw, hwGood, hnw, hrw⟩ := hGood W.center
  have hfinW : R.DfromR W.center Z.center ≠ ∞ := by
    rwa [R.DfromR_symm]
  have hconvz := R.nested_good_annulus_costs_tendsto_zero Bz C hC
    Z.center W.center hZW htop hzGood hnz hrz
  have hconvw := R.nested_good_annulus_costs_tendsto_zero Bw C hC
    W.center Z.center (Ne.symm hZW) hfinW hwGood hnw hrw
  let U : ℕ → RatCircle := fun n => (Bz (n + 1)).inner
  let V : ℕ → RatCircle := fun n => (Bw (n + 1)).inner
  let Uo : ℕ → RatCircle := fun n => (Bz n).outer
  let Vo : ℕ → RatCircle := fun n => (Bw n).outer
  let Au : ℕ → RatAnnulus := fun n => Bz (n + 1)
  let Av : ℕ → RatAnnulus := fun n => Bw (n + 1)
  have hU : ∀ᶠ n in atTop, (U n).Surrounds Z.center :=
    Eventually.of_forall fun n => (hzGood (n + 1)).1
  have hV : ∀ᶠ n in atTop, (V n).Surrounds W.center :=
    Eventually.of_forall fun n => (hwGood (n + 1)).1
  have hrU : Tendsto (fun n => ((U n).radius : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (inner_radius_tendsto_zero_of_outer Bz hrz)
  have hrV : Tendsto (fun n => ((V n).radius : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (inner_radius_tendsto_zero_of_outer Bw hrw)
  have hOpp := eventually_nested_rational_opposite Z W hZ hW hZW
    Bz Bw (fun n => (hzGood n).1) (fun n => (hwGood n).1)
    hnz hnw hrz hrw
  have hUo : Tendsto (fun n => R.across Z (Uo n)) atTop (𝓝 0) :=
    hZvanish Uo
      (Eventually.of_forall fun n => RatAnnulus.outer_surrounds_of_inner
        (hzGood n).1) hrz
  have hVo : Tendsto (fun n => R.across W (Vo n)) atTop (𝓝 0) :=
    hWvanish Vo
      (Eventually.of_forall fun n => RatAnnulus.outer_surrounds_of_inner
        (hwGood n).1) hrw
  have hAu0 : Tendsto (fun n => R.around (Au n)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hconvz.2
  have hAv0 : Tendsto (fun n => R.around (Av n)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hconvw.2
  have hupp := R.across_zero_le_DfromR_of_good_circles
    Z W hZW U V Uo Vo Au Av hU hV hrU hrV
    (hOpp.mono fun n hn => ⟨hn.1, hn.2.1⟩)
    (hOpp.mono fun n hn => ⟨hn.2.2.1, hn.2.2.2⟩)
    hUo hVo hAu0 hAv0
  exact le_antisymm hupp hlow

end SupercriticalLQGUniqueness.B2.DG20Lim
