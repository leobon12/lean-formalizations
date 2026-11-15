/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.MartingaleFinalGeom

/-!
# Lemma 7.1, terminal capacity: a bounded martingale part bounds the two-seed driver

Packet PROVE-LEMMA71B. Specification, proof of Lemma 7.1 (`source/spec/p193-240.md` L604, p. 225): "Its terminal
capacity cannot be finite. Otherwise the globally defined admissible two-seed driving process would have a bounded
driver on that finite interval, and the elementary Loewner hull bounds would put the entire mapped prefix in a
bounded rectangle, contrary to its limit at `∞`."

This file proves the deterministic half of "would have a bounded driver": for the two-seed word with weights
`ρᴸ, ρᴿ > −2` and the geometric images `Vᴸ = −rightImg(−w) 0`, `Vᴿ = rightImg w 0` of the seeds `0⁻`, `0⁺`, the
driver `w` is bounded on `[0, S]` by a constant depending only on `ρᴸ`, `ρᴿ`, `S` and a bound `C` of the martingale
part `M = w + ½ ρᴸ Vᴸ + ½ ρᴿ Vᴿ` of Theorem 2.4 on `[0, S]`.

## The argument (added mathematical step)

Let `U = max_{[0,t]} w ≥ 0` (attained at `s₁`) and `V = max_{[0,t]} (−w) ≥ 0` (attained at `s₂`), and
`c = 1 + 2√S`. The right image is non-decreasing, above the driver, and at most `c` above the running maximum
(`RealFlow.rightImg_le_add`), so `Vᴿ_{s₁} ∈ [U, U + c]`; likewise `−Vᴸ_{s₂} ∈ [V, V + c]`, and the images of the
other side lie in `[0, ·+ c]`. Reading `|M| ≤ C` at `s₁` and at `s₂` gives, with `a = 1 + ρᴸ/2 > 0`,
`b = 1 + ρᴿ/2 > 0`, `l = ρᴸ⁺`, `r = ρᴿ⁺`:

  `b U ≤ E₁ + (l/2) V`,   `a V ≤ E₂ + (r/2) U`.

Since `ab − lr/4 > 0` (it is `ab` if `l r = 0`, and `1 + ρᴸ/2 + ρᴿ/2` otherwise), both `U` and `V` are bounded
(`le_of_two_linear`), hence so is `|w t| ≤ max U V`.

## Main results

* `le_of_two_linear`: the linear-algebra core;
* `twoSeedBound`: the explicit bound;
* **`abs_le_twoSeedBound`**: `|w t| ≤ twoSeedBound ρᴸ ρᴿ S' C` for `t ∈ [0, S]`, `S ≤ S'`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace InteractingSLE.Sec7.Lemma71B

open MartChar MartChar.RealFlow

/-- **The linear-algebra core.** Two linear inequalities `b U ≤ E₁ + (l/2) V`, `a V ≤ E₂ + (r/2) U` with
`a, b > 0`, `l, r ≥ 0` and `ab − lr/4 > 0` bound `U`. -/
theorem le_of_two_linear {U V a b l r E₁ E₂ : ℝ} (ha : 0 < a) (hl : 0 ≤ l)
    (hD : 0 < a * b - l * r / 4) (h1 : b * U ≤ E₁ + l / 2 * V) (h2 : a * V ≤ E₂ + r / 2 * U) :
    U ≤ (a * E₁ + l / 2 * E₂) / (a * b - l * r / 4) := by
  rw [le_div_iff₀ hD]
  have h1' := mul_le_mul_of_nonneg_left h1 ha.le
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ l / 2)
  nlinarith [h1', h2']

/-- The positive part `ρ⁺`. -/
theorem pos_ab_sub {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR) :
    0 < (1 + rL / 2) * (1 + rR / 2) - max rL 0 * max rR 0 / 4 := by
  have ha : 0 < 1 + rL / 2 := by linarith
  have hb : 0 < 1 + rR / 2 := by linarith
  rcases le_total rL 0 with h | h
  · rw [max_eq_right h, zero_mul, zero_div, sub_zero]
    exact mul_pos ha hb
  · rcases le_total rR 0 with h' | h'
    · rw [max_eq_right h', mul_zero, zero_div, sub_zero]
      exact mul_pos ha hb
    · rw [max_eq_left h, max_eq_left h']
      nlinarith

/-- The constant `c = 1 + 2√S` of the right-image bound on `[0, S]`. -/
def capConst (S : ℝ) : ℝ := 1 + 2 * Real.sqrt S

/-- The first linear constant `E₁ = C + (|ρᴿ|/2 + ρᴸ⁺/2) c`. -/
def eOne (rL rR S C : ℝ) : ℝ := C + (|rR| / 2 + max rL 0 / 2) * capConst S

/-- The second linear constant `E₂ = C + (|ρᴸ|/2 + ρᴿ⁺/2) c`. -/
def eTwo (rL rR S C : ℝ) : ℝ := C + (|rL| / 2 + max rR 0 / 2) * capConst S

/-- **The bound of the two-seed driver** in terms of a bound `C` of its martingale part on `[0, S]`. -/
def twoSeedBound (rL rR S C : ℝ) : ℝ :=
  ((1 + rL / 2) * eOne rL rR S C + max rL 0 / 2 * eTwo rL rR S C) /
      ((1 + rL / 2) * (1 + rR / 2) - max rL 0 * max rR 0 / 4) +
    ((1 + rR / 2) * eTwo rL rR S C + max rR 0 / 2 * eOne rL rR S C) /
      ((1 + rR / 2) * (1 + rL / 2) - max rR 0 * max rL 0 / 4)

/-- The right image of `0⁺` at a time `s ≤ t` lies in `[w s, U + c]` when `U` bounds `w` on `[0, t]`. -/
theorem rightImg_mem_of_le {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {s t S U : ℝ}
    (hs : s ∈ Icc 0 t) (htS : t ≤ S) (hU0 : 0 ≤ U) (hU : ∀ u ∈ Icc 0 t, w u ≤ U) :
    0 ≤ rightImg w 0 s ∧ w s ≤ rightImg w 0 s ∧ rightImg w 0 s ≤ U + capConst S := by
  have h00 : rightImg w 0 0 = 0 := rightImg_zero hw hw0 le_rfl
  refine ⟨by have := rightImg_mono_time hw 0 le_rfl hs.1; rwa [h00] at this, le_rightImg hw 0 hs.1, ?_⟩
  have h := rightImg_le_add hw (x := 0) (s := 0) (t := s) (M := U) (ε := 1) le_rfl hs.1 one_pos
    (by rw [h00]; exact hU0) fun u hu => hU u ⟨hu.1, hu.2.trans hs.2⟩
  have hsq : Real.sqrt (s - 0) ≤ Real.sqrt S := Real.sqrt_le_sqrt (by linarith [hs.2])
  simp only [capConst]
  linarith

/-- **A bounded martingale part bounds the two-seed driver** (the deterministic half of "a bounded driver on that
finite interval", proof of Lemma 7.1, p. 225). Let `w` be continuous with `w 0 = 0`, `ρᴸ, ρᴿ > −2`, and let the
martingale part `w − (ρᴸ/2) rightImg(−w) 0 + (ρᴿ/2) rightImg w 0` of the two-seed word be bounded by `C` on
`[0, S]`. Then `|w| ≤ twoSeedBound ρᴸ ρᴿ S' C` on `[0, S]` for every `S' ≥ S`. -/
theorem abs_le_twoSeedBound {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {rL rR : ℝ}
    (hL : -2 < rL) (hR : -2 < rR) {S S' C : ℝ} (hSS : S ≤ S')
    (hM : ∀ t ∈ Icc (0 : ℝ) S,
      |w t - rL / 2 * rightImg (fun s => -w s) 0 t + rR / 2 * rightImg w 0 t| ≤ C)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : |w t| ≤ twoSeedBound rL rR S' C := by
  have hw' : Continuous fun s => -w s := hw.neg
  have hw0' : (fun s => -w s) 0 = 0 := by simp only [hw0, neg_zero]
  have hne : (Icc (0 : ℝ) t).Nonempty := nonempty_Icc.2 ht.1
  obtain ⟨s₁, hs₁, hmax₁⟩ := isCompact_Icc.exists_isMaxOn hne hw.continuousOn
  obtain ⟨s₂, hs₂, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hw'.continuousOn
  set U := w s₁ with hUdef
  set V := -w s₂ with hVdef
  have hU : ∀ u ∈ Icc 0 t, w u ≤ U := fun u hu => hmax₁ hu
  have hV : ∀ u ∈ Icc 0 t, -w u ≤ V := fun u hu => hmax₂ hu
  have h0t : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht.1⟩
  have hU0 : 0 ≤ U := by have := hU 0 h0t; rwa [hw0] at this
  have hV0 : 0 ≤ V := by have := hV 0 h0t; rwa [hw0, neg_zero] at this
  set c := capConst S' with hc
  have htS' : t ≤ S' := ht.2.trans hSS
  set l := max rL 0 with hl
  set r := max rR 0 with hr
  have hl0 : 0 ≤ l := le_max_right _ _
  have hr0 : 0 ≤ r := le_max_right _ _
  have hlL : rL ≤ l := le_max_left _ _
  have hrR : rR ≤ r := le_max_left _ _
  -- the images at `s₁` and `s₂`
  obtain ⟨q₁0, q₁lo, q₁hi⟩ := rightImg_mem_of_le hw hw0 hs₁ htS' hU0 hU
  obtain ⟨p₁0, -, p₁hi⟩ := rightImg_mem_of_le hw' hw0' hs₁ htS' hV0 hV
  obtain ⟨q₂0, -, q₂hi⟩ := rightImg_mem_of_le hw hw0 hs₂ htS' hU0 hU
  obtain ⟨p₂0, p₂lo, p₂hi⟩ := rightImg_mem_of_le hw' hw0' hs₂ htS' hV0 hV
  set q₁ := rightImg w 0 s₁
  set p₁ := rightImg (fun s => -w s) 0 s₁
  set q₂ := rightImg w 0 s₂
  set p₂ := rightImg (fun s => -w s) 0 s₂
  have hS₁ : s₁ ∈ Icc (0 : ℝ) S := ⟨hs₁.1, hs₁.2.trans ht.2⟩
  have hS₂ : s₂ ∈ Icc (0 : ℝ) S := ⟨hs₂.1, hs₂.2.trans ht.2⟩
  have hM₁ := (abs_le.1 (hM s₁ hS₁)).2
  have hM₂ := (abs_le.1 (hM s₂ hS₂)).1
  -- the side bounds
  have hR₁ : rR / 2 * U - |rR| / 2 * c ≤ rR / 2 * q₁ := by
    have hd : 0 ≤ q₁ - U := by linarith
    have hd' : q₁ - U ≤ c := by linarith
    have := neg_abs_le rR
    nlinarith [abs_nonneg rR]
  have hL₁ : rL / 2 * p₁ ≤ l / 2 * (V + c) := by
    have := mul_le_mul_of_nonneg_right hlL p₁0
    nlinarith
  have hL₂ : rL / 2 * V - |rL| / 2 * c ≤ rL / 2 * p₂ := by
    have hd : 0 ≤ p₂ - V := by linarith
    have hd' : p₂ - V ≤ c := by linarith
    have := neg_abs_le rL
    nlinarith [abs_nonneg rL]
  have hR₂ : rR / 2 * q₂ ≤ r / 2 * (U + c) := by
    have := mul_le_mul_of_nonneg_right hrR q₂0
    nlinarith
  -- the two linear inequalities
  have h1 : (1 + rR / 2) * U ≤ eOne rL rR S' C + l / 2 * V := by
    simp only [eOne]
    rw [← hc]
    nlinarith
  have h2 : (1 + rL / 2) * V ≤ eTwo rL rR S' C + r / 2 * U := by
    simp only [eTwo]
    rw [← hc]
    have hw₂ : w s₂ = -V := by rw [hVdef, neg_neg]
    rw [hw₂] at hM₂
    nlinarith
  have hD := pos_ab_sub hL hR
  have hD' : 0 < (1 + rR / 2) * (1 + rL / 2) - max rR 0 * max rL 0 / 4 := by
    have := pos_ab_sub hR hL
    exact this
  have hUle := le_of_two_linear (by linarith : (0 : ℝ) < 1 + rL / 2) hl0 hD h1 h2
  have hVle := le_of_two_linear (by linarith : (0 : ℝ) < 1 + rR / 2) hr0 hD' h2 h1
  have hB1 : 0 ≤ ((1 + rL / 2) * eOne rL rR S' C + max rL 0 / 2 * eTwo rL rR S' C) /
      ((1 + rL / 2) * (1 + rR / 2) - max rL 0 * max rR 0 / 4) := hU0.trans hUle
  have hB2 : 0 ≤ ((1 + rR / 2) * eTwo rL rR S' C + max rR 0 / 2 * eOne rL rR S' C) /
      ((1 + rR / 2) * (1 + rL / 2) - max rR 0 * max rL 0 / 4) := hV0.trans hVle
  have htt : t ∈ Icc 0 t := ⟨ht.1, le_rfl⟩
  rw [abs_le]
  simp only [twoSeedBound]
  constructor
  · have := hV t htt
    linarith
  · have := hU t htt
    linarith

end InteractingSLE.Sec7.Lemma71B
