/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.PartialSums

/-!
# The non-boundary-intersecting regime: boundary heights and force weights (§5)

Packet PROVE-SEC5-A (specification §5, `source/spec/p097-144.md` L676–L1004 and `p145-192.md` L1–L157,
pp. 127–152). The deterministic parameter content of §5.1 and §5.2. Throughout `λ = sleLambda κ = π/√κ`,
`λ' = sleLambda (16/κ)` and `χ = chiC κ = 2/√κ − √κ/2`; for `0 < κ < 4` all three are positive, and
`λ' = λ − (π/2)χ` ((4.2), `Sec4.sleLambda_sixteen_div_eq_sub`). Heights are converted to cumulative force weights by
`Sec4.cumWeightLeft κ h = −h/λ − 1` and `Sec4.cumWeightRight κ h = h/λ − 1`.

* (5.3): `(λ − λ')/χ = π/2` and `(λ' − λ)/χ = −π/2` (`sleLambda_sub_div_chiC`, `sleLambda_sixteen_div_sub_div_chiC`);
  `λ'/λ = κ/4`; the constant `M = πχ/λ = 2 − κ/2 ∈ (0, 2)` of the proof of Proposition 5.9 (`angleWeightBound`).
* Proposition 5.1: the discussion after its statement (`prop51_upper_left_lt`, `prop51_upper_right_gt`), the four
  upper heights of Figure 5.3(b) in its proof (`prop51_proof_heights`), and the meaning of (5.1): it is exactly the
  lower non-hitting data of `h + θχ` (`eq51_iff`), which every angle of (5.3) satisfies when `a, b ≥ λ'`
  (`eq51_of_mem_Icc`).
* Remark 5.3: a constant upper strip height `c` satisfies `c ∉ (−λ, λ)` exactly when the corresponding cumulative
  weight in the half-plane chart is `≥ κ/2 − 2` or `≤ κ/2 − 4` (`rem53_left_iff`, `rem53_right_iff`).
* Proof of Proposition 5.5: under (5.2) and the chosen `a', b'`, the field `h + (θ₁ − π/2)χ` satisfies the
  hypotheses of Proposition 5.1 and the relative angle `θ₂ − θ₁ + π/2 > π/2` satisfies (5.1) (`prop55_reduction`).
* Lemma 5.6: (5.4)–(5.5) and `|θᵢ − θⱼ| ≤ π` make all partial sums of the next piece's force weights at least
  `κ/2 − 2` (`lemma56_left`, `lemma56_right`, as heights of `avLeftHeights`, `avRightHeights`), and such `a, b, a', b'`
  exist for any finite set of angles (`exists_eq54_eq55`).
* Lemma 5.7: for angles in `[−π/2, π/2]`, `−λ − θχ ≤ −λ'` and `λ − θχ ≥ λ'` (`lemma57_heights`).
* Proof of Proposition 5.9: the far heights `−λ' + (θ + π)χ`, `λ' + (θ − π)χ` (Figure 5.8), their weights `κ − 4` and
  `κ/2 − 2` at `θ = π/2` (`prop59_far_weights`), and the strict-height check
  `−λ(1 + κ − 4) − πχ = λ(1 − κ/2) ∈ (−λ, λ)` (`prop59_strict_height`); the weights produced by angle changes,
  `ρ^{i,R} = (χ/λ)(θ_{j−i+1} − θ_{j−i})`, have partial sums bounded by `M` (`abs_sum_angleChangeWeight_le`).
-/

set_option autoImplicit false

noncomputable section

open Real Finset
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Sec5

open Sec4 (cumWeightLeft cumWeightRight)

variable {κ : ℝ}

/-! ### Parameters -/

/-- `λ'/λ = κ/4` (proof of Proposition 5.9, "using `λ'/λ = κ/4`"). -/
theorem sleLambda_sixteen_div_div (hκ : 0 < κ) : sleLambda (16 / κ) / sleLambda κ = κ / 4 := by
  rw [Sec4.sleLambda_sixteen_div hκ, mul_div_assoc, div_self (Sec4.sleLambda_ne_zero hκ), mul_one]

/-- (5.3): `(λ − λ')/χ = π/2`. -/
theorem sleLambda_sub_div_chiC (hκ : 0 < κ) (hκ4 : κ < 4) :
    (sleLambda κ - sleLambda (16 / κ)) / chiC κ = π / 2 := by
  rw [Sec4.sleLambda_sixteen_div_eq_sub hκ, sub_sub_cancel, mul_div_assoc,
    div_self (Sec4.chiC_pos hκ hκ4).ne', mul_one]

/-- (5.3): `(λ' − λ)/χ = −π/2`. -/
theorem sleLambda_sixteen_div_sub_div_chiC (hκ : 0 < κ) (hκ4 : κ < 4) :
    (sleLambda (16 / κ) - sleLambda κ) / chiC κ = -(π / 2) := by
  rw [← neg_sub, neg_div, sleLambda_sub_div_chiC hκ hκ4]

/-- The constant `M = πχ/λ` of the proof of Proposition 5.9. -/
def angleWeightBound (κ : ℝ) : ℝ := π * chiC κ / sleLambda κ

/-- `M = 2 − κ/2`. -/
theorem angleWeightBound_eq (hκ : 0 < κ) : angleWeightBound κ = 2 - κ / 2 :=
  Sec4.pi_mul_chiC_div_sleLambda hκ

theorem angleWeightBound_pos (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < angleWeightBound κ := by
  rw [angleWeightBound_eq hκ]; linarith

/-- `M < 2`. -/
theorem angleWeightBound_lt_two (hκ : 0 < κ) : angleWeightBound κ < 2 := by
  rw [angleWeightBound_eq hκ]; linarith

/-- `χ/λ · π = M`. -/
theorem chiC_div_mul_pi (κ : ℝ) : chiC κ / sleLambda κ * π = angleWeightBound κ := by
  rw [angleWeightBound]; ring

/-! ### Proposition 5.1 -/

/-- Discussion after Proposition 5.1: if `a' ≥ λ'` (in particular under `a' ≥ λ' + πχ`) and `θ < −π/2`, then
`−a' + θχ < −λ`, so `η_θ` does not hit the side of `∂_U𝒮` left of `z₀`. -/
theorem prop51_upper_left_lt (hκ : 0 < κ) (hκ4 : κ < 4) {a' θ : ℝ} (ha' : sleLambda (16 / κ) ≤ a')
    (hθ : θ < -(π / 2)) : -a' + θ * chiC κ < -sleLambda κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [Sec4.sleLambda_sixteen_div_eq_sub hκ] at ha'
  nlinarith

/-- Discussion after Proposition 5.1: if `b' ≥ λ'` and `θ > π/2`, then `b' + θχ > λ`, so `η_θ` does not hit the
side of `∂_U𝒮` right of `z₀`. -/
theorem prop51_upper_right_gt (hκ : 0 < κ) (hκ4 : κ < 4) {b' θ : ℝ} (hb' : sleLambda (16 / κ) ≤ b')
    (hθ : π / 2 < θ) : sleLambda κ < b' + θ * chiC κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [Sec4.sleLambda_sixteen_div_eq_sub hκ] at hb'
  nlinarith

/-- Proof of Proposition 5.1 (Figure 5.3(b)): for `θ > π/2`, `−λ' + θχ > −λ`, `λ' + θχ > λ` and `b' + θχ > λ`, and
the upper heights are ordered `−a' + θχ ≤ −λ' + θχ < λ' + θχ ≤ b' + θχ` (here `a', b' ≥ λ'`). -/
theorem prop51_proof_heights (hκ : 0 < κ) (hκ4 : κ < 4) {a' b' θ : ℝ} (ha' : sleLambda (16 / κ) ≤ a')
    (hb' : sleLambda (16 / κ) ≤ b') (hθ : π / 2 < θ) :
    (-sleLambda κ < -sleLambda (16 / κ) + θ * chiC κ ∧ sleLambda κ < sleLambda (16 / κ) + θ * chiC κ ∧
        sleLambda κ < b' + θ * chiC κ) ∧
      -a' + θ * chiC κ ≤ -sleLambda (16 / κ) + θ * chiC κ ∧
        -sleLambda (16 / κ) + θ * chiC κ < sleLambda (16 / κ) + θ * chiC κ ∧
          sleLambda (16 / κ) + θ * chiC κ ≤ b' + θ * chiC κ := by
  have hl' := Sec4.sleLambda_sixteen_div_pos hκ
  obtain ⟨h1, h2⟩ := Sec4.uc13_heights hκ hκ4 hθ
  exact ⟨⟨h1, h2, prop51_upper_right_gt hκ hκ4 hb' hθ⟩, by linarith, by linarith, by linarith⟩

/-- (5.1) is exactly the lower non-hitting data of `h + θχ` (Remark 4.1, Aux. lemma 22): the cumulative weights of
the lower heights `−a + θχ` and `b + θχ` are at least `κ/2 − 2`. -/
theorem eq51_iff (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ : ℝ} :
    ((sleLambda κ - π * chiC κ - b) / chiC κ ≤ θ ∧ θ ≤ (a + π * chiC κ - sleLambda κ) / chiC κ) ↔
      (κ / 2 - 2 ≤ cumWeightLeft κ (-a + θ * chiC κ) ∧
        κ / 2 - 2 ≤ cumWeightRight κ (b + θ * chiC κ)) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [Sec4.le_cumWeightLeft_iff hκ, Sec4.le_cumWeightRight_iff hκ, div_le_iff₀ hχ, le_div_iff₀ hχ]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- If `a, b ≥ λ'`, every angle `θ ∈ [−π/2, π/2]` of (5.3) satisfies (5.1). -/
theorem eq51_of_mem_Icc (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ : ℝ} (ha : sleLambda (16 / κ) ≤ a)
    (hb : sleLambda (16 / κ) ≤ b) (hθ : θ ∈ Set.Icc (-(π / 2)) (π / 2)) :
    (sleLambda κ - π * chiC κ - b) / chiC κ ≤ θ ∧ θ ≤ (a + π * chiC κ - sleLambda κ) / chiC κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [Sec4.sleLambda_sixteen_div_eq_sub hκ] at ha hb
  rw [div_le_iff₀ hχ, le_div_iff₀ hχ]
  obtain ⟨h1, h2⟩ := hθ
  constructor <;> nlinarith [pi_pos]

/-! ### Remark 5.3 -/

/-- Remark 5.3, left side: an upper strip height `c` on the part of `∂_U𝒮` that the half-plane chart puts on the left
(derivative argument `+π`, height `c + πχ`) satisfies `c ∉ (−λ, λ)` exactly when the cumulative weight there is
at least `κ/2 − 2` or at most `κ/2 − 4`. -/
theorem rem53_left_iff (hκ : 0 < κ) (c : ℝ) :
    c ∉ Set.Ioo (-sleLambda κ) (sleLambda κ) ↔
      κ / 2 - 2 ≤ cumWeightLeft κ (c + π * chiC κ) ∨ cumWeightLeft κ (c + π * chiC κ) ≤ κ / 2 - 4 := by
  have hl := Sec4.sleLambda_pos hκ
  have hw : cumWeightLeft κ (c + π * chiC κ) = -c / sleLambda κ + (κ / 2 - 3) := by
    simp only [cumWeightLeft, neg_add, add_div, Sec4.neg_pi_mul_chiC_div_sleLambda hκ]; ring
  rw [hw, Set.mem_Ioo, not_and_or, not_lt, not_lt]
  have e1 : κ / 2 - 2 ≤ -c / sleLambda κ + (κ / 2 - 3) ↔ c ≤ -sleLambda κ := by
    constructor
    · intro h; have := (le_div_iff₀ hl).1 (show 1 ≤ -c / sleLambda κ by linarith); linarith
    · intro h; have : 1 ≤ -c / sleLambda κ := (le_div_iff₀ hl).2 (by linarith); linarith
  have e2 : -c / sleLambda κ + (κ / 2 - 3) ≤ κ / 2 - 4 ↔ sleLambda κ ≤ c := by
    constructor
    · intro h; have := (div_le_iff₀ hl).1 (show -c / sleLambda κ ≤ -1 by linarith); linarith
    · intro h; have : -c / sleLambda κ ≤ -1 := (div_le_iff₀ hl).2 (by linarith); linarith
  rw [e1, e2]

/-- Remark 5.3, right side: an upper strip height `c` that the chart puts on the right (derivative argument `−π`,
height `c − πχ`) satisfies `c ∉ (−λ, λ)` exactly when the cumulative weight there is at least `κ/2 − 2` or at most
`κ/2 − 4`. -/
theorem rem53_right_iff (hκ : 0 < κ) (c : ℝ) :
    c ∉ Set.Ioo (-sleLambda κ) (sleLambda κ) ↔
      κ / 2 - 2 ≤ cumWeightRight κ (c - π * chiC κ) ∨ cumWeightRight κ (c - π * chiC κ) ≤ κ / 2 - 4 := by
  have hl := Sec4.sleLambda_pos hκ
  have hw : cumWeightRight κ (c - π * chiC κ) = c / sleLambda κ + (κ / 2 - 3) := by
    simp only [cumWeightRight, sub_div, Sec4.pi_mul_chiC_div_sleLambda hκ]; ring
  rw [hw, Set.mem_Ioo, not_and_or, not_lt, not_lt, or_comm]
  have e1 : κ / 2 - 2 ≤ c / sleLambda κ + (κ / 2 - 3) ↔ sleLambda κ ≤ c := by
    constructor
    · intro h; have := (le_div_iff₀ hl).1 (show 1 ≤ c / sleLambda κ by linarith); linarith
    · intro h; have : 1 ≤ c / sleLambda κ := (le_div_iff₀ hl).2 (by linarith); linarith
  have e2 : c / sleLambda κ + (κ / 2 - 3) ≤ κ / 2 - 4 ↔ c ≤ -sleLambda κ := by
    constructor
    · intro h; have := (div_le_iff₀ hl).1 (show c / sleLambda κ ≤ -1 by linarith); linarith
    · intro h; have : c / sleLambda κ ≤ -1 := (div_le_iff₀ hl).2 (by linarith); linarith
  rw [e1, e2]

/-! ### Proposition 5.5 -/

/-- **Proof of Proposition 5.5, the reduction to Proposition 5.1.** Assume (5.2),
`(λ − b)/χ ≤ θ₁ < θ₂ ≤ (a + πχ − λ)/χ`, and choose `a' ≥ λ' + (θ₁ + π/2)χ`, `b' ≥ λ' + (3π/2 − θ₁)χ`. With the shift
`s = (θ₁ − π/2)χ` the field `h + s` has upper data `−a' + s ≤ −λ' − πχ` left of `z₀` and `b' + s ≥ λ' + πχ` right
of it, and lower data `−a + s ≤ −λ'`, `b + s ≥ λ'`: these are the hypotheses `a' + (−s), b' + s ≥ λ' + πχ` and
`a − s, b + s ≥ λ'` of Proposition 5.1. The relative angle `θ₂ − θ₁ + π/2` exceeds `π/2` and satisfies (5.1) for
the shifted data. -/
theorem prop55_reduction (hκ : 0 < κ) (hκ4 : κ < 4) {a b a' b' θ₁ θ₂ : ℝ}
    (h1 : (sleLambda κ - b) / chiC κ ≤ θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ ≤ (a + π * chiC κ - sleLambda κ) / chiC κ)
    (ha' : sleLambda (16 / κ) + (θ₁ + π / 2) * chiC κ ≤ a')
    (hb' : sleLambda (16 / κ) + (3 * π / 2 - θ₁) * chiC κ ≤ b') :
    (sleLambda (16 / κ) + π * chiC κ ≤ a' - (θ₁ - π / 2) * chiC κ ∧
        sleLambda (16 / κ) + π * chiC κ ≤ b' + (θ₁ - π / 2) * chiC κ ∧
        sleLambda (16 / κ) ≤ a - (θ₁ - π / 2) * chiC κ ∧
        sleLambda (16 / κ) ≤ b + (θ₁ - π / 2) * chiC κ) ∧
      π / 2 < θ₂ - θ₁ + π / 2 ∧
        (sleLambda κ - π * chiC κ - (b + (θ₁ - π / 2) * chiC κ)) / chiC κ ≤ θ₂ - θ₁ + π / 2 ∧
          θ₂ - θ₁ + π / 2 ≤
            (a - (θ₁ - π / 2) * chiC κ + π * chiC κ - sleLambda κ) / chiC κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [div_le_iff₀ hχ] at h1
  rw [le_div_iff₀ hχ] at h2
  have h12' : θ₁ * chiC κ < θ₂ * chiC κ := mul_lt_mul_of_pos_right h12 hχ
  rw [Sec4.sleLambda_sixteen_div_eq_sub hκ] at ha' hb' ⊢
  refine ⟨⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩, by linarith, ?_, ?_⟩
  · rw [div_le_iff₀ hχ]; nlinarith [pi_pos]
  · rw [le_div_iff₀ hχ]; nlinarith [pi_pos]

/-! ### Lemma 5.6 -/

/-- The lower-boundary heights seen by the next piece, of angle `θ`, of an angle-varying flow line (Figure 5.5, right
panel; Figure 5.8), on the left of the seed in boundary order after mapping out the earlier pieces with angles `prev`
(most recent first) and sending the target `z₀` to `∞`: the left sides `−λ − (φ − θ)χ` of the earlier pieces, the
lower strip height `−a + θχ`, and the upper strip height `−a' + (θ + π)χ` left of `z₀` (derivative argument `+π`). -/
def avLeftHeights (κ a a' θ : ℝ) (prev : List ℝ) : List ℝ :=
  prev.map (fun φ => -sleLambda κ - (φ - θ) * chiC κ) ++
    [-a + θ * chiC κ, -a' + (θ + π) * chiC κ]

/-- The heights on the right of the seed: `λ − (φ − θ)χ`, `b + θχ`, and `b' + (θ − π)χ` right of `z₀`
(derivative argument `−π`). -/
def avRightHeights (κ b b' θ : ℝ) (prev : List ℝ) : List ℝ :=
  prev.map (fun φ => sleLambda κ - (φ - θ) * chiC κ) ++
    [b + θ * chiC κ, b' + (θ - π) * chiC κ]

/-- **Lemma 5.6, left partial sums.** If `|φ − θ| ≤ π` for every earlier angle and (5.4)–(5.5) hold for `θ`, every
left height of the next piece has cumulative weight at least `κ/2 − 2`. -/
theorem lemma56_left (hκ : 0 < κ) (hκ4 : κ < 4) {a a' θ : ℝ} {prev : List ℝ}
    (hprev : ∀ φ ∈ prev, |φ - θ| ≤ π)
    (h54 : κ / 2 - 2 ≤ (a - θ * chiC κ) / sleLambda κ - 1)
    (h55 : κ / 2 - 2 ≤ (a' - (θ + π) * chiC κ) / sleLambda κ - 1) :
    ∀ h ∈ avLeftHeights κ a a' θ prev, κ / 2 - 2 ≤ cumWeightLeft κ h := by
  have hχ := Sec4.chiC_pos hκ hκ4
  intro h hh
  simp only [avLeftHeights, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hh
  rcases hh with ⟨φ, hφ, rfl⟩ | rfl | rfl
  · rw [Sec4.le_cumWeightLeft_iff hκ]
    have := (abs_le.1 (hprev φ hφ)).1
    nlinarith
  · simpa only [cumWeightLeft, neg_add, neg_neg, sub_eq_add_neg, neg_div, add_div] using h54
  · simpa only [cumWeightLeft, neg_add, neg_neg, sub_eq_add_neg, neg_div, add_div] using h55

/-- **Lemma 5.6, right partial sums.** -/
theorem lemma56_right (hκ : 0 < κ) (hκ4 : κ < 4) {b b' θ : ℝ} {prev : List ℝ}
    (hprev : ∀ φ ∈ prev, |φ - θ| ≤ π)
    (h54 : κ / 2 - 2 ≤ (b + θ * chiC κ) / sleLambda κ - 1)
    (h55 : κ / 2 - 2 ≤ (b' + (θ - π) * chiC κ) / sleLambda κ - 1) :
    ∀ h ∈ avRightHeights κ b b' θ prev, κ / 2 - 2 ≤ cumWeightRight κ h := by
  have hχ := Sec4.chiC_pos hκ hκ4
  intro h hh
  simp only [avRightHeights, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hh
  rcases hh with ⟨φ, hφ, rfl⟩ | rfl | rfl
  · rw [Sec4.le_cumWeightRight_iff hκ]
    have := (abs_le.1 (hprev φ hφ)).2
    nlinarith
  · exact h54
  · exact h55

/-- After Lemma 5.6: "for any fixed choice of `θⱼ` we can always pick `a, b, a', b'` large enough so that (5.4) and
(5.5) hold". -/
theorem exists_eq54_eq55 (hκ : 0 < κ) (S : Finset ℝ) :
    ∃ a b a' b' : ℝ, ∀ θ ∈ S,
      (κ / 2 - 2 ≤ (a - θ * chiC κ) / sleLambda κ - 1 ∧
        κ / 2 - 2 ≤ (b + θ * chiC κ) / sleLambda κ - 1) ∧
      κ / 2 - 2 ≤ (a' - (θ + π) * chiC κ) / sleLambda κ - 1 ∧
        κ / 2 - 2 ≤ (b' + (θ - π) * chiC κ) / sleLambda κ - 1 := by
  have hl := Sec4.sleLambda_pos hκ
  set R : ℝ := ∑ θ ∈ S, |θ * chiC κ| + |π * chiC κ| + |κ / 2 - 1| * sleLambda κ with hR
  have hθR : ∀ θ ∈ S, |θ * chiC κ| ≤ ∑ θ ∈ S, |θ * chiC κ| := fun θ hθ =>
    single_le_sum (f := fun θ => |θ * chiC κ|) (fun _ _ => abs_nonneg _) hθ
  have hc : (κ / 2 - 1) * sleLambda κ ≤ |κ / 2 - 1| * sleLambda κ :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hl.le
  have key : ∀ u : ℝ, |u| ≤ R - |κ / 2 - 1| * sleLambda κ →
      κ / 2 - 2 ≤ (2 * R + u) / sleLambda κ - 1 := by
    intro u hu
    rw [le_sub_iff_add_le, le_div_iff₀ hl]
    have := neg_abs_le u
    have : 0 ≤ |κ / 2 - 1| * sleLambda κ := mul_nonneg (abs_nonneg _) hl.le
    have : 0 ≤ ∑ θ ∈ S, |θ * chiC κ| := sum_nonneg fun _ _ => abs_nonneg _
    have := abs_nonneg (π * chiC κ)
    linarith
  have hpi := abs_nonneg (π * chiC κ)
  refine ⟨2 * R, 2 * R, 2 * R, 2 * R, fun θ hθ => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · rw [sub_eq_add_neg]; refine key _ ?_
    rw [abs_neg]; have := hθR θ hθ; linarith
  · refine key _ ?_; have := hθR θ hθ; linarith
  · rw [sub_eq_add_neg]; refine key _ ?_
    rw [abs_neg, add_mul]
    have := hθR θ hθ; have := abs_add_le (θ * chiC κ) (π * chiC κ); linarith
  · refine key _ ?_
    rw [sub_mul, sub_eq_add_neg]
    have := hθR θ hθ; have := abs_add_le (θ * chiC κ) (-(π * chiC κ))
    rw [abs_neg] at this; linarith

/-! ### Lemma 5.7 -/

/-- Proof of Lemma 5.7: for `θ ∈ [−π/2, π/2]`, `−λ − θχ ≤ −λ'` and `λ − θχ ≥ λ'`. -/
theorem lemma57_heights (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ : θ ∈ Set.Icc (-(π / 2)) (π / 2)) :
    -sleLambda κ - θ * chiC κ ≤ -sleLambda (16 / κ) ∧
      sleLambda (16 / κ) ≤ sleLambda κ - θ * chiC κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  obtain ⟨h1, h2⟩ := hθ
  rw [Sec4.sleLambda_sixteen_div_eq_sub hκ]
  constructor <;> nlinarith

/-! ### Proof of Proposition 5.9: heights and weights -/

/-- Figure 5.8 at angle `θ = π/2`: the far heights `−λ' + (θ + π)χ` and `λ' + (θ − π)χ` have total left and right
weights `κ − 4` and `κ/2 − 2` ("using `λ'/λ = κ/4` and `πχ/λ = 2 − κ/2`"). -/
theorem prop59_far_weights (hκ : 0 < κ) :
    cumWeightLeft κ (-sleLambda (16 / κ) + (π / 2 + π) * chiC κ) = κ - 4 ∧
      cumWeightRight κ (sleLambda (16 / κ) + (π / 2 - π) * chiC κ) = κ / 2 - 2 := by
  have hl := Sec4.sleLambda_ne_zero hκ
  have hm := Sec4.pi_mul_chiC_div_sleLambda hκ
  have hq := sleLambda_sixteen_div_div hκ
  constructor
  · have : cumWeightLeft κ (-sleLambda (16 / κ) + (π / 2 + π) * chiC κ) =
        sleLambda (16 / κ) / sleLambda κ - 3 / 2 * (π * chiC κ / sleLambda κ) - 1 := by
      simp only [cumWeightLeft]; field_simp; ring
    rw [this, hm, hq]; ring
  · have : cumWeightRight κ (sleLambda (16 / κ) + (π / 2 - π) * chiC κ) =
        sleLambda (16 / κ) / sleLambda κ - 1 / 2 * (π * chiC κ / sleLambda κ) - 1 := by
      simp only [cumWeightRight]; field_simp; ring
    rw [this, hm, hq]; ring

/-- **The strict-height check** (proof of Proposition 5.9): mapping the half-plane to the strip by
`Φ(z) = π⁻¹ Log((z − x₋)/(w − x₋))` (derivative argument `−π` on `(−∞, x₋)`), the far left height with total weight
`κ − 4` becomes the upper strip height `−λ(1 + κ − 4) − πχ = λ(1 − κ/2)`, which lies in `(−λ, λ)` for `0 < κ < 4`. -/
theorem prop59_strict_height (hκ : 0 < κ) (hκ4 : κ < 4) :
    -sleLambda κ * (1 + (κ - 4)) - π * chiC κ = sleLambda κ * (1 - κ / 2) ∧
      sleLambda κ * (1 - κ / 2) ∈ Set.Ioo (-sleLambda κ) (sleLambda κ) := by
  have hl := Sec4.sleLambda_pos hκ
  refine ⟨by rw [Sec4.pi_mul_chiC hκ]; ring, ?_, ?_⟩ <;> nlinarith

/-- The far heights are preserved: at any angle `θ` the upper far heights of Figure 5.8 are
`−λ' + (θ + π)χ` and `λ' + (θ − π)χ`; at `θ = π/2` these are `−λ' + 3πχ/2` and `λ' − πχ/2`. -/
theorem prop59_far_heights_half_pi :
    -sleLambda (16 / κ) + (π / 2 + π) * chiC κ = -sleLambda (16 / κ) + 3 * π * chiC κ / 2 ∧
      sleLambda (16 / κ) + (π / 2 - π) * chiC κ = sleLambda (16 / κ) - π * chiC κ / 2 := by
  constructor <;> ring

/-- The weight produced by the angle change between consecutive angles (proof of Proposition 5.9):
`ρ^{i,R} = (χ/λ)(θ_{j−i+1} − θ_{j−i})`; `ρ^{i,L} = −ρ^{i,R}`. Here `φ i = θ_{j−i}` lists the angles backwards from
the current one. -/
def angleChangeWeight (κ : ℝ) (φ : ℕ → ℝ) (i : ℕ) : ℝ := chiC κ / sleLambda κ * (φ i - φ (i + 1))

/-- The partial sums of the angle-change weights telescope: `∑_{i<m} ρ^{i+1,R} = (χ/λ)(θ_j − θ_{j−m})`. -/
theorem sum_angleChangeWeight (κ : ℝ) (φ : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range m, angleChangeWeight κ φ i = chiC κ / sleLambda κ * (φ 0 - φ m) := by
  simp only [angleChangeWeight, ← mul_sum, sum_range_sub']

/-- "Every partial sum of these left weights has absolute value at most `M`, and the same is true of the right
weights after omitting the first one": for angles in `[−π/2, π/2]`, every partial sum of consecutive angle-change
weights, starting at any index, has absolute value at most `M = πχ/λ`. -/
theorem abs_sum_angleChangeWeight_le (hκ : 0 < κ) (hκ4 : κ < 4) {φ : ℕ → ℝ}
    (hφ : ∀ i, φ i ∈ Set.Icc (-(π / 2)) (π / 2)) (k m : ℕ) :
    |∑ i ∈ range m, angleChangeWeight κ (fun i => φ (k + i)) i| ≤ angleWeightBound κ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hl := Sec4.sleLambda_pos hκ
  rw [sum_angleChangeWeight, abs_mul, abs_of_pos (div_pos hχ hl), ← chiC_div_mul_pi]
  refine mul_le_mul_of_nonneg_left ?_ (div_pos hχ hl).le
  obtain ⟨h1, h2⟩ := hφ (k + 0)
  obtain ⟨h3, h4⟩ := hφ (k + m)
  rw [abs_le]; constructor <;> linarith

/-- The first right weight lies in `[−M, M] ⊂ (−2, ∞)`. -/
theorem angleChangeWeight_mem (hκ : 0 < κ) (hκ4 : κ < 4) {φ : ℕ → ℝ}
    (hφ : ∀ i, φ i ∈ Set.Icc (-(π / 2)) (π / 2)) (i : ℕ) :
    angleChangeWeight κ φ i ∈ Set.Icc (-angleWeightBound κ) (angleWeightBound κ) ∧
      -2 < angleChangeWeight κ φ i := by
  have h := abs_sum_angleChangeWeight_le hκ hκ4 hφ i 1
  simp only [range_one, sum_singleton] at h
  have h' : angleChangeWeight κ (fun j => φ (i + j)) 0 = angleChangeWeight κ φ i := by
    simp [angleChangeWeight]
  rw [h'] at h
  have := angleWeightBound_lt_two hκ
  exact ⟨abs_le.1 h, by linarith [(abs_le.1 h).1]⟩

end Sec5

end InteractingSLE
