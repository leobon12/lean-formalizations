import SupercriticalLQGUniqueness.B2.DG20Lim.NestedGoodCostConv
import SupercriticalLQGUniqueness.B2.DG20Lim.AroundLimit

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.triangle_of_nested_good_annuli
    (R : RData) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hGood : ∀ y : ℂ, ∃ B : ℕ → RatAnnulus,
      (∀ n, (B n).inner.Surrounds y ∧
        R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
      (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
      Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0))
    (x y z : ℂ) :
    R.DfromR x z ≤ R.DfromR x y + R.DfromR y z := by
  by_cases hxy : x = y
  · subst x
    simp only [R.DfromR_self, zero_add, le_refl]
  by_cases hyz : y = z
  · subst z
    simp only [R.DfromR_self, add_zero, le_refl]
  by_cases htop : R.DfromR x y + R.DfromR y z = ∞
  · rw [htop]
    exact le_top
  have hfinite : R.DfromR y x ≠ ∞ := by
    rw [R.DfromR_symm]
    intro h
    apply htop
    simp [h]
  obtain ⟨B, hBg, hBn, hBr⟩ := hGood y
  have hconv := R.nested_good_annulus_costs_tendsto_zero B C hC y x
    (Ne.symm hxy) hfinite hBg hBn hBr
  have houter : ∀ᶠ n in atTop, (B n).outer.Surrounds y := by
    filter_upwards with n
    exact RatAnnulus.outer_surrounds_of_inner (hBg n).1
  have hxout : ∀ᶠ n in atTop, x ∉ (B n).outer.closedDisk := by
    have hyopen : y ∈ ({x} : Set ℂ)ᶜ := by simpa using (Ne.symm hxy)
    have hev := RatCircle.eventually_closedDisk_subset_open
      isClosed_singleton.isOpen_compl hyopen
      (fun n => (B n).outer) houter hBr
    filter_upwards [hev] with n hn hx
    exact (hn hx) (by simp)
  have hzout : ∀ᶠ n in atTop, z ∉ (B n).outer.closedDisk := by
    have hyopen : y ∈ ({z} : Set ℂ)ᶜ := by simpa using hyz
    have hev := RatCircle.eventually_closedDisk_subset_open
      isClosed_singleton.isOpen_compl hyopen
      (fun n => (B n).outer) houter hBr
    filter_upwards [hev] with n hn hz
    exact (hn hz) (by simp)
  have hle : ∀ᶠ n in atTop,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR z y + R.around (B n) := by
    filter_upwards [hxout, hzout] with n hx hz
    exact R.DfromR_le_add_around (B n) x z y y
      (Or.inr ⟨(hBg n).1.2, hx⟩)
      (Or.inr ⟨(hBg n).1.2, hz⟩)
  have hlim : Tendsto
      (fun n => R.DfromR x y + R.DfromR z y + R.around (B n))
      atTop (𝓝 (R.DfromR x y + R.DfromR z y + 0)) :=
    (tendsto_const_nhds.add tendsto_const_nhds).add hconv.2
  have hbound := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle
  simpa only [add_zero, R.DfromR_symm z y] using hbound

end SupercriticalLQGUniqueness.B2.DG20Lim
