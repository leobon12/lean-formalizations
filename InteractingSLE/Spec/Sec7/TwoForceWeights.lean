/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Heights

/-!
# Two boundary force points: the seed weights (§7.1)

Packet PROVE-SEC7-A (specification §7.1, `source/spec/p193-240.md` L539–L912 and `p241-288.md` L1–L271,
pp. 221–252). The deterministic parameter content of §7.1. Throughout `λ = sleLambda κ = π/√κ` and
`χ = chiC κ = 2/√κ − √κ/2`; for `0 < κ < 4` both are positive (`Sec4.sleLambda_pos`, `Sec4.chiC_pos`).

* **(CPF2)** (Lemma 7.1): the middle (angle-zero) flow line between the flow lines of angles `θ₁ < 0 < θ₂`
  sees, in a pocket, the boundary heights `λ − θ₂χ` on the left and `−λ − θ₁χ` on the right (Figure 7.1),
  i.e. the seed weights `ρᴸ = θ₂χ/λ − 2`, `ρᴿ = −θ₁χ/λ − 2` (`cpf2_rhoL_eq`, `cpf2_rhoR_eq`), both
  `> −2` (`neg_two_lt_cpf2RhoL`, `neg_two_lt_cpf2RhoR`).
* The remark after Lemma 7.2 (p. 227): "as `θ₁ < 0 < θ₂` vary, (CPF2) ranges over every pair
  `ρᴸ, ρᴿ > −2`, because `χ > 0` for `0 < κ < 4`" (`exists_angles_cpf2_eq`, and the image statement
  `range_cpf2_eq`).
* Proposition 7.4's parameter remark (p. 244): its hypotheses `θ₁ > −(λ + b)/χ`, `θ₂ < (a + λ)/χ` and
  `θ₁ < θ₂` are exactly the conditions that the three force-point weights
  `(b + θ₁χ)/λ − 1`, `(a − θ₂χ)/λ − 1` and `(θ₂ − θ₁)χ/λ − 2` exceed `−2` (`prop74_weights_iff`).
-/

set_option autoImplicit false

noncomputable section

open Real
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Sec7

open Sec4

/-! ### (CPF2): the seed weights of the middle flow line in a pocket -/

/-- The left seed weight `ρᴸ = θ₂χ/λ − 2` of (CPF2). -/
def cpf2RhoL (κ θ₂ : ℝ) : ℝ := θ₂ * chiC κ / sleLambda κ - 2

/-- The right seed weight `ρᴿ = −θ₁χ/λ − 2` of (CPF2). -/
def cpf2RhoR (κ θ₁ : ℝ) : ℝ := -(θ₁ * chiC κ) / sleLambda κ - 2

/-- (CPF2) from the left pocket height: the height `λ − θ₂χ` on the left side of the pocket
(Figure 7.1, the image of the left outer flow line `η_{θ₂}`) is the cumulative left weight
`cumWeightLeft κ (λ − θ₂χ) = θ₂χ/λ − 2`. -/
theorem cpf2_rhoL_eq {κ : ℝ} (hκ : 0 < κ) (θ₂ : ℝ) :
    cumWeightLeft κ (sleLambda κ - θ₂ * chiC κ) = cpf2RhoL κ θ₂ := by
  have := sleLambda_ne_zero hκ
  simp only [cumWeightLeft, cpf2RhoL]
  field_simp
  ring

/-- (CPF2) from the right pocket height: the height `−λ − θ₁χ` on the right side of the pocket
(Figure 7.1, the image of the right outer flow line `η_{θ₁}`) is the cumulative right weight
`cumWeightRight κ (−λ − θ₁χ) = −θ₁χ/λ − 2`. -/
theorem cpf2_rhoR_eq {κ : ℝ} (hκ : 0 < κ) (θ₁ : ℝ) :
    cumWeightRight κ (-sleLambda κ - θ₁ * chiC κ) = cpf2RhoR κ θ₁ := by
  have := sleLambda_ne_zero hκ
  simp only [cumWeightRight, cpf2RhoR]
  field_simp
  ring

/-- For `0 < κ < 4`: `ρᴸ = θ₂χ/λ − 2 > −2` iff `θ₂ > 0`. -/
theorem neg_two_lt_cpf2RhoL_iff {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (θ₂ : ℝ) :
    -2 < cpf2RhoL κ θ₂ ↔ 0 < θ₂ := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  have e : -2 < cpf2RhoL κ θ₂ ↔ 0 < θ₂ * chiC κ / sleLambda κ := by
    simp only [cpf2RhoL]; constructor <;> intro h <;> linarith
  rw [e, div_pos_iff_of_pos_right hl, mul_pos_iff_of_pos_right hχ]

/-- For `0 < κ < 4`: `ρᴿ = −θ₁χ/λ − 2 > −2` iff `θ₁ < 0`. -/
theorem neg_two_lt_cpf2RhoR_iff {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (θ₁ : ℝ) :
    -2 < cpf2RhoR κ θ₁ ↔ θ₁ < 0 := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  have e : -2 < cpf2RhoR κ θ₁ ↔ 0 < -(θ₁ * chiC κ) / sleLambda κ := by
    simp only [cpf2RhoR]; constructor <;> intro h <;> linarith
  rw [e, div_pos_iff_of_pos_right hl, neg_pos]
  exact ⟨fun h => neg_of_mul_neg_left h hχ.le, fun h => mul_neg_of_neg_of_pos h hχ⟩

theorem neg_two_lt_cpf2RhoL {κ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₂ : 0 < θ₂) :
    -2 < cpf2RhoL κ θ₂ :=
  (neg_two_lt_cpf2RhoL_iff hκ hκ4 θ₂).2 hθ₂

theorem neg_two_lt_cpf2RhoR {κ θ₁ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) :
    -2 < cpf2RhoR κ θ₁ :=
  (neg_two_lt_cpf2RhoR_iff hκ hκ4 θ₁).2 hθ₁

/-- The remark after Lemma 7.2 (p. 227): for `0 < κ < 4`, every admissible two-seed pair
`ρᴸ, ρᴿ > −2` is the (CPF2) pair of some angles `θ₁ < 0 < θ₂`, namely `θ₂ = (ρᴸ + 2)λ/χ` and
`θ₁ = −(ρᴿ + 2)λ/χ`. -/
theorem exists_angles_cpf2_eq {κ ρL ρR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hL : -2 < ρL)
    (hR : -2 < ρR) :
    ∃ θ₁ θ₂ : ℝ, θ₁ < 0 ∧ 0 < θ₂ ∧ cpf2RhoL κ θ₂ = ρL ∧ cpf2RhoR κ θ₁ = ρR := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  refine ⟨-((ρR + 2) * sleLambda κ / chiC κ), (ρL + 2) * sleLambda κ / chiC κ, ?_, ?_, ?_, ?_⟩
  · have : 0 < (ρR + 2) * sleLambda κ / chiC κ := div_pos (mul_pos (by linarith) hl) hχ
    linarith
  · exact div_pos (mul_pos (by linarith) hl) hχ
  · simp only [cpf2RhoL]
    field_simp
    ring
  · simp only [cpf2RhoR]
    field_simp
    ring

/-- The image of `{θ₁ < 0 < θ₂}` under (CPF2) is exactly `{ρᴸ > −2} × {ρᴿ > −2}` (for `0 < κ < 4`). -/
theorem range_cpf2_eq {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    (fun θ : ℝ × ℝ => (cpf2RhoL κ θ.2, cpf2RhoR κ θ.1)) '' (Set.Iio 0 ×ˢ Set.Ioi 0) =
      Set.Ioi (-2) ×ˢ Set.Ioi (-2) := by
  ext ⟨ρL, ρR⟩
  simp only [Set.mem_image, Set.mem_prod, Set.mem_Iio, Set.mem_Ioi, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨θ₁, θ₂, ⟨h₁, h₂⟩, rfl, rfl⟩
    exact ⟨neg_two_lt_cpf2RhoL hκ hκ4 h₂, neg_two_lt_cpf2RhoR hκ hκ4 h₁⟩
  · rintro ⟨hL, hR⟩
    obtain ⟨θ₁, θ₂, h₁, h₂, e₂, e₁⟩ := exists_angles_cpf2_eq hκ hκ4 hL hR
    exact ⟨θ₁, θ₂, ⟨h₁, h₂⟩, e₂, e₁⟩

/-! ### Proposition 7.4: the hypotheses on the angles are the weight conditions -/

/-- The right seed weight `(b + θ₁χ)/λ − 1` of the flow line `η_{θ₁}` (boundary value `b` right of
`0`) exceeds `−2` iff `θ₁ > −(λ + b)/χ` (for `0 < κ < 4`). -/
theorem prop74_right_weight_iff {κ b θ₁ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    -2 < (b + θ₁ * chiC κ) / sleLambda κ - 1 ↔ -(sleLambda κ + b) / chiC κ < θ₁ := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  rw [div_lt_iff₀ hχ, show (-2 : ℝ) = -1 - 1 by norm_num, sub_lt_sub_iff_right,
    lt_div_iff₀ hl]
  constructor <;> intro h <;> linarith

/-- The left seed weight `(a − θ₂χ)/λ − 1` of the flow line `η_{θ₂}` (boundary value `−a` left of
`0`) exceeds `−2` iff `θ₂ < (a + λ)/χ` (for `0 < κ < 4`). -/
theorem prop74_left_weight_iff {κ a θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    -2 < (a - θ₂ * chiC κ) / sleLambda κ - 1 ↔ θ₂ < (a + sleLambda κ) / chiC κ := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  rw [lt_div_iff₀ hχ, show (-2 : ℝ) = -1 - 1 by norm_num, sub_lt_sub_iff_right,
    lt_div_iff₀ hl]
  constructor <;> intro h <;> linarith

/-- The interaction weight `(θ₂ − θ₁)χ/λ − 2` between the two flow lines exceeds `−2` iff
`θ₁ < θ₂` (for `0 < κ < 4`). -/
theorem prop74_middle_weight_iff {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    -2 < (θ₂ - θ₁) * chiC κ / sleLambda κ - 2 ↔ θ₁ < θ₂ := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  have e : -2 < (θ₂ - θ₁) * chiC κ / sleLambda κ - 2 ↔ 0 < (θ₂ - θ₁) * chiC κ / sleLambda κ := by
    constructor <;> intro h <;> linarith
  rw [e, div_pos_iff_of_pos_right hl, mul_pos_iff_of_pos_right hχ, sub_pos]

/-- Proposition 7.4's parameter remark (p. 244): "the hypothesis on `θ₁, θ₂` is to ensure that the
values of the weights of the force points associated with `η_{θ₁}, η_{θ₂}` exceed `−2`". The three
weights of the conditional laws in Proposition 7.4 —
`SLE_κ((θ₂ − θ₁)χ/λ − 2; (b + θ₁χ)/λ − 1)` for `η_{θ₁}` given `η_{θ₂}` and
`SLE_κ((a − θ₂χ)/λ − 1; (θ₂ − θ₁)χ/λ − 2)` for `η_{θ₂}` given `η_{θ₁}` — all exceed `−2` iff
`θ₁ < θ₂`, `θ₁ > −(λ + b)/χ` and `θ₂ < (a + λ)/χ`. -/
theorem prop74_weights_iff {κ a b θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    (-2 < (θ₂ - θ₁) * chiC κ / sleLambda κ - 2 ∧ -2 < (b + θ₁ * chiC κ) / sleLambda κ - 1 ∧
        -2 < (a - θ₂ * chiC κ) / sleLambda κ - 1) ↔
      (θ₁ < θ₂ ∧ -(sleLambda κ + b) / chiC κ < θ₁ ∧ θ₂ < (a + sleLambda κ) / chiC κ) := by
  rw [prop74_middle_weight_iff hκ hκ4, prop74_right_weight_iff hκ hκ4,
    prop74_left_weight_iff hκ hκ4]

end Sec7

end InteractingSLE
