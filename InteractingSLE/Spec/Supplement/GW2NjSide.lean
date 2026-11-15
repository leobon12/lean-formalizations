/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WmPos
import InteractingSLE.Spec.Supplement.GW2NgJunc
import InteractingSLE.Spec.Supplement.GB6CoordBCurve

/-!
# The counterflow's right side in the relative chart: real points stay left of the junction (D81, part 1)

Packet PROVE-GW2-NEARIMG2, decision D81. In GB6's relative chart (`relBdry U s`, the counterflow tip at `∞`), the
counterflow's right side is the ray beyond the right junction `jR = labelL U s 0 = −1/markPosL(0)` (`jROfRec`). Every
physical point off the closed retained hull is sent either into `ℍ` (points of `ℍ`, `relBdry_mem_H_iff`) or to a real
point `≤ jR`:
* a real point `y > 0` goes to the returned left mark `labelL U s (−1/y)` (`GW2Wm.labelL_eq_relBdry`), which is at
  most `labelL U s 0` (monotone on `(−∞, 0]`, `GW2Wm.monotoneOn_labelL`);
* a real point `y < 0` goes to a returned right mark `labelR U s (−1/y) ≤ 0`; `y = 0` goes to `0`.

* **`re_relBdry_le_labelL_zero`**, **`relBdry_le_of_im_eq_zero`** (one safe point);
* `labelL_zero_eq_jROfRec`, `labelL_zero_pos`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2Ni

open Restart Exist.Staged Exist.StagedLaw Supp8.GB6 Supp8.GB6.CoordB GW2Wm

variable {U : ℝ → ℝ} {s : ℝ}

/-- The right junction is the returned left mark of the seed. -/
theorem labelL_zero_eq_jROfRec (r : RecData) : labelL (rdrv r) (rtime r) 0 = jROfRec r := rfl

theorem labelL_zero_pos (hneg : markPosL U s 0 < 0) : 0 < labelL U s 0 := by
  unfold labelL
  exact neg_pos.2 (inv_lt_zero.2 hneg)

/-- **A real safe point goes left of the right junction.** -/
theorem re_relBdry_le_labelL_zero (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (hneg : markPosL U s 0 < 0)
    {y : ℝ} (hyA : (y : ℂ) ∉ closure (Supp8.Q3Rel.invHull U s)) : (relBdry U s y).re ≤ labelL U s 0 := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [← labelR_eq_relBdry hU hU0 hs hy hyA]
    have hp : 0 ≤ -y⁻¹ := (neg_pos.2 (inv_lt_zero.2 hy)).le
    have hm := GW1W.markPos_nonneg hU hU0 hs hp
    unfold labelR
    have : -(markPos U s (-y⁻¹))⁻¹ ≤ 0 := neg_nonpos.2 (inv_nonneg.2 hm)
    exact this.trans (labelL_zero_pos hneg).le
  · subst hy
    rw [Complex.ofReal_zero, relBdry_zero hU hU0 hs, Complex.zero_re]
    exact (labelL_zero_pos hneg).le
  · rw [← labelL_eq_relBdry hU hU0 hs hy hyA]
    exact monotoneOn_labelL hU hU0 hs hneg (neg_nonpos.2 (inv_nonneg.2 hy.le)) (le_refl (0 : ℝ))
      (neg_nonpos.2 (inv_nonneg.2 hy.le))

/-- **A safe point with a real chart value goes left of the right junction**: if `relBdry z` is real, then `z` is a
real safe point and `relBdry z ≤ jR`. -/
theorem relBdry_le_of_im_eq_zero (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (hneg : markPosL U s 0 < 0)
    {z : ℂ} (hz : z ∈ relSafe U s) (him : (relBdry U s z).im = 0) :
    (relBdry U s z).re ≤ labelL U s 0 := by
  have hzH : z ∉ H := fun h => by
    have := (relBdry_mem_H_iff hU hU0 hs hz).2 h
    exact absurd him (ne_of_gt this)
  have hzim : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzim])
  have hzA : ((z.re : ℝ) : ℂ) ∉ closure (Supp8.Q3Rel.invHull U s) := by rw [← hzr]; exact hz.2
  rw [hzr]
  exact re_relBdry_le_labelL_zero hU hU0 hs hneg hzA

end InteractingSLE.Theorem14.GW2Ni
