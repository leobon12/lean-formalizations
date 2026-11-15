/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowWords

/-!
# Theorem R.7's proof, first paragraph: the actual incoming angles and the side classification

Packet PROVE-R7. Supplement §5.7, proof of Theorem R.7 (`source/spec/p433-480.md` L1058–L1063, p. 477), as repeated in
the repaired Theorem 2.1 (`source/external/AstraIG1/ig1_ztip_elimination.txt` lines 503–508):

> Set the actual incoming angles by `r_L = (1/2 − θ_R/π)A − 2`, `r_R = (1/2 + θ_L/π)A − 2`. They satisfy
> `θ_R < θ_L`, `θ_R < π/2`, and `θ_L > −π/2`: indeed `r_L + r_R + 4 > A` follows from the displayed parameter
> hypotheses. A weight below `d` gives a strictly contained side, equality gives the corresponding certified extremal
> side, and a weight above `d` gives an outer side. There is no upper bound on the two weights. […] If neither side is
> outer, at least one is extremal and the same claims are already the contained reference of Aux. 131.

Conventions (supplement §5.1, p. 471): `k > 4`, `κ = 16/k`, `A = k/2 − 2` (`Sec7.counterflowA κ`), `d = A − 2`. The
angles are the inverses (RS13.6) of the weight formulas (CF9.5) already formalized for Lemma 7.25 and Aux. lemma 131:
`θ_R = Sec7.rs136Theta1 κ r_L`, `θ_L = Sec7.rs136Theta2 κ r_R` (`Spec/Sec7/CounterflowWords.lean`, reused).

* `counterflowA_sixteen_div`: `A = k/2 − 2` for `κ = 16/k`.
* `cf95RhoL_thetaR`, `cf95RhoR_thetaL`: the angles produce the weights.
* `thetaR_lt_pi_div_two`, `neg_pi_div_two_lt_thetaL`, `thetaR_lt_thetaL` (with `four_add_lt_of_le_max`: `r_L + r_R + 4 > A`).
* The side classification of the right arm (angle `θ_R`, extremal value `−π/2`) and of the left arm (angle `θ_L`,
  extremal value `π/2`): `rL_lt_d_iff`, `rL_eq_d_iff`, `d_lt_rL_iff` and `rR_lt_d_iff`, `rR_eq_d_iff`, `d_lt_rR_iff`;
  strictly contained sides have angles in `(−π/2, π/2)` (`thetaR_mem_Ioo_of_lt`, `thetaL_mem_Ioo_of_lt`).
* `cs131_of_not_outer`: if neither side is outer, the pair lies in the sector (CS13.1) of Aux. lemma 131.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Real

namespace InteractingSLE

namespace R7

open Sec7

variable {k rL rR : ℝ}

/-- `A = κ'/2 − 2 = k/2 − 2` for the flow parameter `κ = 16/k` (supplement §5.1). -/
theorem counterflowA_sixteen_div (hk : 0 < k) : counterflowA (16 / k) = k / 2 - 2 := by
  have e : (16 : ℝ) / (16 / k) = k := by field_simp
  unfold counterflowA
  rw [e]

theorem sixteen_div_pos (hk : 0 < k) : 0 < 16 / k := div_pos (by norm_num) hk

theorem sixteen_div_lt_four (hk4 : 4 < k) : 16 / k < 4 := by
  rw [div_lt_iff₀ (by linarith)]
  linarith

theorem counterflowA_sixteen_div_pos (hk4 : 4 < k) : 0 < counterflowA (16 / k) :=
  counterflowA_pos (sixteen_div_pos (by linarith)) (sixteen_div_lt_four hk4)

/-- The right incoming angle `θ_R` of Theorem R.7's proof. -/
def thetaR (k rL : ℝ) : ℝ := rs136Theta1 (16 / k) rL

/-- The left incoming angle `θ_L` of Theorem R.7's proof. -/
def thetaL (k rR : ℝ) : ℝ := rs136Theta2 (16 / k) rR

/-- `r_L = (1/2 − θ_R/π)A − 2`. -/
theorem cf95RhoL_thetaR (hk4 : 4 < k) (rL : ℝ) : cf95RhoL (16 / k) (thetaR k rL) = rL :=
  cf95RhoL_rs136Theta1 (sixteen_div_pos (by linarith)) (sixteen_div_lt_four hk4) rL

/-- `r_R = (1/2 + θ_L/π)A − 2`. -/
theorem cf95RhoR_thetaL (hk4 : 4 < k) (rR : ℝ) : cf95RhoR (16 / k) (thetaL k rR) = rR :=
  cf95RhoR_rs136Theta2 (sixteen_div_pos (by linarith)) (sixteen_div_lt_four hk4) rR

/-- The explicit forms `θ_R = π/2 − π(r_L + 2)/A` and `θ_L = π(r_R + 2)/A − π/2`. -/
theorem thetaR_eq (k rL : ℝ) : thetaR k rL = π / 2 - π * ((rL + 2) / counterflowA (16 / k)) := by
  rw [thetaR, rs136Theta1]; ring

theorem thetaL_eq (k rR : ℝ) : thetaL k rR = π * ((rR + 2) / counterflowA (16 / k)) - π / 2 := by
  rw [thetaL, rs136Theta2]; ring

/-- "`r_L + r_R + 4 > A` follows from the displayed parameter hypotheses". -/
theorem four_add_lt_of_le_max (hk : 0 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 ≤ max rL rR) :
    counterflowA (16 / k) < rL + rR + 4 := by
  rw [counterflowA_sixteen_div hk]
  rcases le_max_iff.1 hmax with h | h <;> linarith

theorem thetaR_lt_pi_div_two (hk4 : 4 < k) (hL : -2 < rL) : thetaR k rL < π / 2 := by
  rw [thetaR_eq]
  have := div_pos (by linarith : (0 : ℝ) < rL + 2) (counterflowA_sixteen_div_pos hk4)
  nlinarith [Real.pi_pos]

theorem neg_pi_div_two_lt_thetaL (hk4 : 4 < k) (hR : -2 < rR) : -(π / 2) < thetaL k rR := by
  rw [thetaL_eq]
  have := div_pos (by linarith : (0 : ℝ) < rR + 2) (counterflowA_sixteen_div_pos hk4)
  nlinarith [Real.pi_pos]

/-- `θ_R < θ_L` exactly when `r_L + r_R + 4 > A`. -/
theorem thetaR_lt_thetaL_iff (hk4 : 4 < k) :
    thetaR k rL < thetaL k rR ↔ counterflowA (16 / k) < rL + rR + 4 := by
  have hA := counterflowA_sixteen_div_pos hk4
  rw [thetaR_eq, thetaL_eq]
  have e : π * ((rR + 2) / counterflowA (16 / k)) - π / 2 - (π / 2 - π * ((rL + 2) / counterflowA (16 / k))) =
      π * ((rL + rR + 4) / counterflowA (16 / k) - 1) := by ring
  rw [← sub_pos, e, mul_pos_iff_of_pos_left Real.pi_pos, sub_pos, one_lt_div hA]

/-- "They satisfy `θ_R < θ_L`, `θ_R < π/2`, and `θ_L > −π/2`." -/
theorem thetaR_lt_thetaL (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 ≤ max rL rR) :
    thetaR k rL < thetaL k rR :=
  (thetaR_lt_thetaL_iff hk4).2 (four_add_lt_of_le_max (by linarith) hL hR hmax)

/-! ### The side classification -/

/-- `(r + 2)/A` compared with `1` is `r` compared with `d = A − 2`. -/
theorem div_lt_one_iff_lt_d (hk4 : 4 < k) (r : ℝ) : (r + 2) / counterflowA (16 / k) < 1 ↔ r < k / 2 - 4 := by
  rw [div_lt_one (counterflowA_sixteen_div_pos hk4), counterflowA_sixteen_div (by linarith)]
  constructor <;> intro h <;> linarith

theorem div_eq_one_iff_eq_d (hk4 : 4 < k) (r : ℝ) : (r + 2) / counterflowA (16 / k) = 1 ↔ r = k / 2 - 4 := by
  rw [div_eq_one_iff_eq (counterflowA_sixteen_div_pos hk4).ne', counterflowA_sixteen_div (by linarith)]
  constructor <;> intro h <;> linarith

/-- Right side, "a weight below `d` gives a strictly contained side": `r_L < d ↔ θ_R > −π/2`. -/
theorem rL_lt_d_iff (hk4 : 4 < k) : rL < k / 2 - 4 ↔ -(π / 2) < thetaR k rL := by
  rw [thetaR_eq, ← div_lt_one_iff_lt_d hk4]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- Right side, "equality gives the corresponding certified extremal side": `r_L = d ↔ θ_R = −π/2`. -/
theorem rL_eq_d_iff (hk4 : 4 < k) : rL = k / 2 - 4 ↔ thetaR k rL = -(π / 2) := by
  rw [thetaR_eq, ← div_eq_one_iff_eq_d hk4]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have hπ := Real.pi_pos
    have : π * ((rL + 2) / counterflowA (16 / k)) = π * 1 := by linarith
    exact mul_left_cancel₀ hπ.ne' this

/-- Right side, "a weight above `d` gives an outer side": `r_L > d ↔ θ_R < −π/2`. -/
theorem d_lt_rL_iff (hk4 : 4 < k) : k / 2 - 4 < rL ↔ thetaR k rL < -(π / 2) := by
  rw [← not_le, ← not_le, le_iff_lt_or_eq, le_iff_lt_or_eq, rL_lt_d_iff hk4, rL_eq_d_iff hk4, eq_comm]

/-- Left side: `r_R < d ↔ θ_L < π/2`. -/
theorem rR_lt_d_iff (hk4 : 4 < k) : rR < k / 2 - 4 ↔ thetaL k rR < π / 2 := by
  rw [thetaL_eq, ← div_lt_one_iff_lt_d hk4]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- Left side: `r_R = d ↔ θ_L = π/2`. -/
theorem rR_eq_d_iff (hk4 : 4 < k) : rR = k / 2 - 4 ↔ thetaL k rR = π / 2 := by
  rw [thetaL_eq, ← div_eq_one_iff_eq_d hk4]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have hπ := Real.pi_pos
    have : π * ((rR + 2) / counterflowA (16 / k)) = π * 1 := by linarith
    exact mul_left_cancel₀ hπ.ne' this

/-- Left side: `r_R > d ↔ θ_L > π/2`. -/
theorem d_lt_rR_iff (hk4 : 4 < k) : k / 2 - 4 < rR ↔ π / 2 < thetaL k rR := by
  rw [← not_le, ← not_le, le_iff_lt_or_eq, le_iff_lt_or_eq, rR_lt_d_iff hk4, rR_eq_d_iff hk4]

/-- A strictly contained right side has its angle in `(−π/2, π/2)`. -/
theorem thetaR_mem_Ioo_of_lt (hk4 : 4 < k) (hL : -2 < rL) (hd : rL < k / 2 - 4) :
    thetaR k rL ∈ Ioo (-(π / 2)) (π / 2) :=
  ⟨(rL_lt_d_iff hk4).1 hd, thetaR_lt_pi_div_two hk4 hL⟩

/-- A strictly contained left side has its angle in `(−π/2, π/2)`. -/
theorem thetaL_mem_Ioo_of_lt (hk4 : 4 < k) (hR : -2 < rR) (hd : rR < k / 2 - 4) :
    thetaL k rR ∈ Ioo (-(π / 2)) (π / 2) :=
  ⟨neg_pi_div_two_lt_thetaL hk4 hR, (rR_lt_d_iff hk4).1 hd⟩

/-- "If neither side is outer, at least one is extremal and the same claims are already the contained reference of
Aux. 131": the pair lies in the sector (CS13.1), `−2 < r_L, r_R ≤ d`, `r_L + r_R > d − 2`, with one weight equal to
`d`. -/
theorem cs131_of_not_outer (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 ≤ max rL rR)
    (hL' : rL ≤ k / 2 - 4) (hR' : rR ≤ k / 2 - 4) :
    (rL = k / 2 - 4 ∨ rR = k / 2 - 4) ∧
      (-2 < rL ∧ rL ≤ counterflowA (16 / k) - 2 ∧ -2 < rR ∧ rR ≤ counterflowA (16 / k) - 2 ∧
        counterflowA (16 / k) - 2 - 2 < rL + rR) := by
  rw [counterflowA_sixteen_div (by linarith)]
  rcases le_max_iff.1 hmax with h | h
  · exact ⟨Or.inl (le_antisymm hL' h), hL, by linarith, hR, by linarith, by linarith⟩
  · exact ⟨Or.inr (le_antisymm hR' h), hL, by linarith, hR, by linarith, by linarith⟩

/-- The angle form of the previous statement (Aux. lemma 131's (CS13.1) ⟺ `−π/2 ≤ θ_R < θ_L ≤ π/2`, `Sec7.cs131_iff`). -/
theorem cs131_angles_of_not_outer (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : k / 2 - 4 ≤ max rL rR)
    (hL' : rL ≤ k / 2 - 4) (hR' : rR ≤ k / 2 - 4) :
    -(π / 2) ≤ thetaR k rL ∧ thetaR k rL < thetaL k rR ∧ thetaL k rR ≤ π / 2 ∧ thetaR k rL < π / 2 ∧
      -(π / 2) < thetaL k rR :=
  (cs131_iff (sixteen_div_pos (by linarith)) (sixteen_div_lt_four hk4)).1
    (cs131_of_not_outer hL hR hmax hL' hR').2

end R7

end InteractingSLE
