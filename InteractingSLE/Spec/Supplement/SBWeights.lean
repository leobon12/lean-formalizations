/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S7Weights

/-!
# Supplement §28: the weight algebra of the sewn barriers SB1–SB5

Packet PROVE-T14-SB (specification supplement §28, `source/spec/p625-671.md` L86–L196, pp. 629–635). Throughout
`0 < κ < 4`, `λ = sleLambda κ`, `χ = chiC κ`, `φ = −π/2` (the lower-walk angle), `Λ = λ − πχ/2`, `c_κ = κ/2 − 2`,
`d_κ = κ/2 − 4`. An angle-`θ` flow sees a boundary height `H` as the left cumulative weight
`cumWeightLeft κ (H + θχ) = −(H + θχ)/λ − 1` and the right cumulative weight `cumWeightRight κ (H + θχ) =
(H + θχ)/λ − 1` (`Sec4.cumWeightLeft`, `Sec4.cumWeightRight`); the angle gap is `Supp7.angleGap κ θ₁ θ₂ =
(θ₂ − θ₁)χ/λ`.

* **`πχ < 2λ`** (`pi_mul_chiC_lt`, SB5's "strict last inequality uses `πχ = 2λ − 2Λ < 2λ`"), so `Λ > 0`
  (`bigLambda_pos`).
* **(SB4.1) for the angles of GW2** (`sb41_of_mem_Icc`, `sb41_of_mem_Ioo`): two angles in `[−π/2, π/2]`, not both
  extreme on opposite sides, differ by less than `2λ/χ`; in particular any two angles of a set `Θ ⊂ (−π/2, π/2)`.
  With (SB4.1) the new upper weights on old sides have differences `(ψ − ψ_j)χ/λ > −2` (`neg_two_lt_angleGap`).
* **The protected middle word for a lower restart** (p. 629) and **(SB3.1)** (p. 633): a height `H ≤ −λ − φχ = −Λ`
  gives the lower flow the left cumulative weight `≥ 0 > c_κ` (`sb31`, `protected_lower_left`).
* **(SB2.1)** (p. 632): an old upper-right side of angle `ψ_j > φ` (height `λ − ψ_jχ`) gives the lower flow the left
  weight `−2 + (ψ_j − φ)χ/λ > −2`; an old upper-left side (height `−λ − ψ_jχ`) gives `(ψ_j − φ)χ/λ > 0` (`sb21`).
* **SB1's transition marks** (p. 630): a lower cumulative weight `> −2` is `> d_κ` (`dStar_lt_of_neg_two_lt`).
* **(SB5.1) and its consequences** (p. 635): on a height `−λ − πχ/2 < H ≤ −Λ` the upper walk (angle `π/2`) has right
  weight `> −2`, and every angle `θ ≤ π/2` has left weight `> −2`; so the initial middle word is doubly admissible
  (`sb51_upper_right`, `sb51_left`, `sb51_doubly_admissible`). The lower-arc rule gives the upper bound `H ≤ −Λ`
  (`le_neg_bigLambda_of_low`).
-/

set_option autoImplicit false

noncomputable section

open Real
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Theorem14

namespace SB

open Sec4 Supp7

variable {κ : ℝ}

/-! ### `πχ < 2λ` and (SB4.1) -/

/-- `πχ < 2λ` for `κ > 0` (SB5: "`πχ = 2λ − 2Λ < 2λ`"; `πχ = (2 − κ/2)λ`). -/
theorem pi_mul_chiC_lt (hκ : 0 < κ) : π * chiC κ < 2 * sleLambda κ := by
  have hl := sleLambda_pos hκ
  rw [pi_mul_chiC hκ]
  nlinarith

/-- `Λ = λ − πχ/2 > 0` for `κ > 0`. -/
theorem bigLambda_pos (hκ : 0 < κ) : 0 < sleLambda κ - π / 2 * chiC κ := by
  have := pi_mul_chiC_lt hκ
  linarith

/-- `π < 2λ/χ` for `0 < κ < 4`. -/
theorem pi_lt_two_mul_sleLambda_div (hκ : 0 < κ) (hκ4 : κ < 4) : π < 2 * sleLambda κ / chiC κ := by
  rw [lt_div_iff₀ (chiC_pos hκ hκ4)]
  exact pi_mul_chiC_lt hκ

/-- **(SB4.1) for the GW2 angles**: two angles in `[−π/2, π/2]` with `|ψ − ψ'| < π` (e.g. not one at `−π/2` and the
other at `π/2`) satisfy `|ψ − ψ'| < 2λ/χ`. -/
theorem sb41_of_abs_lt_pi (hκ : 0 < κ) (hκ4 : κ < 4) {ψ ψ' : ℝ} (h : |ψ - ψ'| < π) :
    |ψ - ψ'| < 2 * sleLambda κ / chiC κ :=
  h.trans (pi_lt_two_mul_sleLambda_div hκ hκ4)

/-- **(SB4.1)** for angles in `(−π/2, π/2]`: their differences are `< π`, hence `< 2λ/χ`. -/
theorem sb41_of_mem_Ioc (hκ : 0 < κ) (hκ4 : κ < 4) {ψ ψ' : ℝ} (hψ : ψ ∈ Set.Ioc (-(π / 2)) (π / 2))
    (hψ' : ψ' ∈ Set.Ioc (-(π / 2)) (π / 2)) : |ψ - ψ'| < 2 * sleLambda κ / chiC κ := by
  refine sb41_of_abs_lt_pi hκ hκ4 (abs_lt.2 ⟨?_, ?_⟩)
  · linarith [hψ.1, hψ'.2]
  · linarith [hψ.2, hψ'.1]

/-- **(SB4.1)** for angles in `[−π/2, π/2)` (the reflected barrier). -/
theorem sb41_of_mem_Ico (hκ : 0 < κ) (hκ4 : κ < 4) {ψ ψ' : ℝ} (hψ : ψ ∈ Set.Ico (-(π / 2)) (π / 2))
    (hψ' : ψ' ∈ Set.Ico (-(π / 2)) (π / 2)) : |ψ - ψ'| < 2 * sleLambda κ / chiC κ := by
  refine sb41_of_abs_lt_pi hκ hκ4 (abs_lt.2 ⟨?_, ?_⟩)
  · linarith [hψ.1, hψ'.2]
  · linarith [hψ.2, hψ'.1]

/-- **(SB4.1)** for angles in `(−π/2, π/2)` (the angle set `Θ` of GW2). -/
theorem sb41_of_mem_Ioo (hκ : 0 < κ) (hκ4 : κ < 4) {ψ ψ' : ℝ} (hψ : ψ ∈ Set.Ioo (-(π / 2)) (π / 2))
    (hψ' : ψ' ∈ Set.Ioo (-(π / 2)) (π / 2)) : |ψ - ψ'| < 2 * sleLambda κ / chiC κ :=
  sb41_of_mem_Ioc hκ hκ4 ⟨hψ.1, hψ.2.le⟩ ⟨hψ'.1, hψ'.2.le⟩

/-- **SB4's old-side weights**: under (SB4.1) the difference `(ψ − ψ_j)χ/λ` of a new upper angle `ψ` and an old one
`ψ_j` exceeds `−2` (SB4's proof: "the new upper weights on its own old sides have the differences
`(ψ − ψ_j)χ/λ > −2` supplied by (SB4.1)"). -/
theorem neg_two_lt_angleGap (hκ : 0 < κ) (hκ4 : κ < 4) {ψ ψ' : ℝ}
    (h : |ψ - ψ'| < 2 * sleLambda κ / chiC κ) : -2 < angleGap κ ψ' ψ := by
  have hl := sleLambda_pos hκ
  have hc := chiC_pos hκ hκ4
  have h1 : -(ψ - ψ') < 2 * sleLambda κ / chiC κ := neg_lt.1 (abs_lt.1 h).1
  have h2 : -(ψ - ψ') * chiC κ < 2 * sleLambda κ := (lt_div_iff₀ hc).1 h1
  rw [angleGap, lt_div_iff₀ hl]
  linarith

/-! ### The protected middle word and (SB3.1) -/

/-- **(SB3.1)** (p. 633): a middle height `H ≤ −λ − φχ` (an ordinary lower side or a low connector) gives the lower
flow (angle `φ`) the left cumulative weight `−(H + φχ)/λ − 1 ≥ 0 > c_κ`. -/
theorem sb31 (hκ : 0 < κ) (hκ4 : κ < 4) {H φ : ℝ} (hH : H ≤ -sleLambda κ - φ * chiC κ) :
    0 ≤ cumWeightLeft κ (H + φ * chiC κ) ∧ κ / 2 - 2 < cumWeightLeft κ (H + φ * chiC κ) := by
  have hl := sleLambda_pos hκ
  have h0 : 0 ≤ cumWeightLeft κ (H + φ * chiC κ) := by
    simp only [cumWeightLeft]
    rw [sub_nonneg, le_div_iff₀ hl]
    linarith
  exact ⟨h0, by linarith⟩

/-- **The protected middle word for a lower restart** (p. 629): an exposed left side of an earlier angle-`−π/2`
segment (height `−Λ`) or a low real connector (height `H ≤ −Λ`) has the lower-flow left cumulative weight
`−(H − πχ/2)/λ − 1 ≥ 0 > κ/2 − 2`. -/
theorem protected_lower_left (hκ : 0 < κ) (hκ4 : κ < 4) {H : ℝ}
    (hH : H ≤ -(sleLambda κ - π / 2 * chiC κ)) :
    0 ≤ cumWeightLeft κ (H + -(π / 2) * chiC κ) ∧ κ / 2 - 2 < cumWeightLeft κ (H + -(π / 2) * chiC κ) :=
  sb31 hκ hκ4 (by linarith)

/-! ### (SB2.1) -/

/-- **(SB2.1)** (p. 632): for an old upper angle `ψ_j > φ`, the lower flow (angle `φ`) has on an old upper-right side
(height `λ − ψ_jχ`) the left weight `−2 + (ψ_j − φ)χ/λ > −2`, and on an old upper-left side (height `−λ − ψ_jχ`)
the protected weight `(ψ_j − φ)χ/λ > 0`. -/
theorem sb21 (hκ : 0 < κ) (hκ4 : κ < 4) {φ ψ : ℝ} (hφψ : φ < ψ) :
    cumWeightLeft κ ((sleLambda κ - ψ * chiC κ) + φ * chiC κ) = -2 + angleGap κ φ ψ ∧
      -2 < cumWeightLeft κ ((sleLambda κ - ψ * chiC κ) + φ * chiC κ) ∧
      cumWeightLeft κ ((-sleLambda κ - ψ * chiC κ) + φ * chiC κ) = angleGap κ φ ψ ∧
      0 < cumWeightLeft κ ((-sleLambda κ - ψ * chiC κ) + φ * chiC κ) := by
  obtain ⟨-, h2, h3, -⟩ := g2_left_weights hκ φ ψ
  have hd := angleGap_pos hκ hκ4 hφψ
  refine ⟨by rw [h2]; ring, by rw [h2]; linarith, h3, by rw [h3]; exact hd⟩

/-- **SB1's transition marks** (p. 630): a lower cumulative weight `> −2` is `> d_κ = κ/2 − 4` for `κ < 4`. -/
theorem dStar_lt_of_neg_two_lt (hκ4 : κ < 4) {s : ℝ} (hs : -2 < s) : κ / 2 - 4 < s :=
  (dStar_lt_neg_two hκ4).trans hs

/-! ### (SB5.1) -/

/-- **The lower-arc rule** (GW1, BW2.1; `lowerArcRoots`): an outward height with `H − πχ/2 ≤ −λ` satisfies
`H ≤ −Λ = −λ + πχ/2`, the upper bound of (SB5.1). -/
theorem le_neg_bigLambda_of_low {H : ℝ} (hH : H - π / 2 * chiC κ ≤ -sleLambda κ) :
    H ≤ -(sleLambda κ - π / 2 * chiC κ) := by
  linarith

/-- **(SB5.1), the upper walk** (p. 635): on a height `H > −λ − πχ/2` the upper walk (angle `π/2`) has right
cumulative weight `(H + πχ/2)/λ − 1 > −2`. -/
theorem sb51_upper_right (hκ : 0 < κ) {H : ℝ} (hH : -sleLambda κ - π / 2 * chiC κ < H) :
    -2 < cumWeightRight κ (H + π / 2 * chiC κ) := by
  have hl := sleLambda_pos hκ
  simp only [cumWeightRight]
  rw [show -2 < (H + π / 2 * chiC κ) / sleLambda κ - 1 ↔ -1 < (H + π / 2 * chiC κ) / sleLambda κ by
    constructor <;> intro h <;> linarith, lt_div_iff₀ hl]
  linarith

/-- **(SB5.1), a schedule angle** (p. 635): on a height `H ≤ −Λ`, every angle `θ ≤ π/2` has
`H + θχ ≤ −λ + πχ < λ`, hence left cumulative weight `−(H + θχ)/λ − 1 > −2`. -/
theorem sb51_left (hκ : 0 < κ) (hκ4 : κ < 4) {H θ : ℝ} (hH : H ≤ -(sleLambda κ - π / 2 * chiC κ))
    (hθ : θ ≤ π / 2) : -2 < cumWeightLeft κ (H + θ * chiC κ) := by
  have hl := sleLambda_pos hκ
  have hc := chiC_pos hκ hκ4
  have hlt := pi_mul_chiC_lt hκ
  have hθc : θ * chiC κ ≤ π / 2 * chiC κ := mul_le_mul_of_nonneg_right hθ hc.le
  have hsum : H + θ * chiC κ < sleLambda κ := by linarith
  simp only [cumWeightLeft]
  rw [show -2 < -(H + θ * chiC κ) / sleLambda κ - 1 ↔ -1 < -(H + θ * chiC κ) / sleLambda κ by
    constructor <;> intro h <;> linarith, lt_div_iff₀ hl]
  linarith

/-- **(SB5.1): the initial middle word is doubly admissible** (p. 635: "the whole initial middle word is doubly
admissible for every schedule angle, which is a special case of SB4's hybrid condition"): on a height
`−λ − πχ/2 < H ≤ −Λ`, the upper walk's right weight and every angle-`θ` (`θ ≤ π/2`) left weight exceed `−2`. -/
theorem sb51_doubly_admissible (hκ : 0 < κ) (hκ4 : κ < 4) {H : ℝ}
    (hlo : -sleLambda κ - π / 2 * chiC κ < H) (hhi : H ≤ -(sleLambda κ - π / 2 * chiC κ)) {θ : ℝ}
    (hθ : θ ≤ π / 2) :
    -2 < cumWeightRight κ (H + π / 2 * chiC κ) ∧ -2 < cumWeightLeft κ (H + θ * chiC κ) :=
  ⟨sb51_upper_right hκ hlo, sb51_left hκ hκ4 hhi hθ⟩

end SB

end Theorem14

end InteractingSLE
