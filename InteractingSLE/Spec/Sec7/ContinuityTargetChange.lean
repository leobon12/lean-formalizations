/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import QuantumZipper.Common.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Analysis.Complex.Basic

/-!
# The target change of the revised induction (§7.3, (C1)–(C2))

Packet PROVE-SEC7-C (specification §7.3, "Revised induction for Theorem 1.3, `0 < κ < 4`",
`source/spec/p337-384.md` L843–L875, pp. 378–380). When all `N ≥ 2` active force groups lie on one side,
reflected to the right at `0 ≤ x₁ < x₂ < ⋯ < x_N`, the induction targets the second marked point by

  `ψ(z) = z / (x₂ − z)`,                                                                   (C1)

which fixes the seed, takes `x₂` to the new target at infinity and the old target to `−1`. The transformed finite
marks are the sole right mark `ψ(x₁)` and the `N − 1` left marks `−1, ψ(x_N), ψ(x_{N−1}), …, ψ(x₃)`        (C2)
with weights `κ − 6 − S_N, ρ_N, …, ρ₃` (`S_j = ρ₁ + ⋯ + ρ_j`), so the side totals are `ρ₁` and `κ − 6 − S₂`, and
there are exactly `N` finite groups.

This file proves the deterministic content of (C1)–(C2):

* `targetChange x₂` (`ψ`) and its inverse `targetChangeInv x₂` (`w ↦ x₂ w / (1 + w)`): they are mutually inverse
  off the poles (`targetChangeInv_targetChange`, `targetChange_targetChangeInv`), `ψ(0) = 0`, `ψ` maps `ℍ` onto `ℍ`
  (`bijOn_targetChange_H`); the old target goes to `−1` (`tendsto_targetChange_cobounded`), the new target `x₂` to
  infinity (`tendsto_norm_targetChange_nhdsNE`), and the inverse image of a neighbourhood of `−1` goes to infinity
  (`tendsto_targetChangeInv_nhdsNE_neg_one`);
* on the real line `ψ` is strictly increasing on `(−∞, x₂)` and on `(x₂, ∞)`; `ψ(x) ≥ 0` for `0 ≤ x < x₂`; `ψ(x) < −1`
  for `x > x₂`; and a swallowing point `q < −1` pulls back to `ψ⁻¹(q) > x₂` (`lt_targetChangeInvReal`), the
  geometric fact behind "the original trace has swallowed at least its first two force-point groups";
* the transformed force word `targetChangeWord` of (C2): it is an ordered force word (`isOrderedForceWord_…`), its
  side totals are `κ − 6 − S₂` and `ρ₁` (`sum_targetChangeWeightL`, `sum_targetChangeWeightR`), it has exactly `N`
  finite groups, its left positions are strictly decreasing and negative, and `ψ⁻¹` maps every transformed mark
  back to the original mark it came from.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology
open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

/-! ### The Möbius map `ψ(z) = z/(x₂ − z)` of (C1) -/

/-- The target change (C1), `ψ(z) = z / (x₂ − z)`. -/
def targetChange (x₂ : ℝ) (z : ℂ) : ℂ := z / ((x₂ : ℂ) - z)

/-- The inverse of the target change, `ψ⁻¹(w) = x₂ w / (1 + w)`. -/
def targetChangeInv (x₂ : ℝ) (w : ℂ) : ℂ := (x₂ : ℂ) * w / (1 + w)

variable {x₂ : ℝ}

@[simp] theorem targetChange_zero (x₂ : ℝ) : targetChange x₂ 0 = 0 := by simp [targetChange]

@[simp] theorem targetChangeInv_zero (x₂ : ℝ) : targetChangeInv x₂ 0 = 0 := by simp [targetChangeInv]

/-- `ψ⁻¹ ∘ ψ = id` off the pole `x₂`. -/
theorem targetChangeInv_targetChange (hx : x₂ ≠ 0) {z : ℂ} (hz : z ≠ x₂) :
    targetChangeInv x₂ (targetChange x₂ z) = z := by
  have h1 : (x₂ : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have hx' : (x₂ : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  have h2 : 1 + z / ((x₂ : ℂ) - z) = x₂ / ((x₂ : ℂ) - z) := by field_simp; ring
  simp only [targetChangeInv, targetChange, h2]
  field_simp

/-- `ψ ∘ ψ⁻¹ = id` off the pole `−1`. -/
theorem targetChange_targetChangeInv (hx : x₂ ≠ 0) {w : ℂ} (hw : w ≠ -1) :
    targetChange x₂ (targetChangeInv x₂ w) = w := by
  have h1 : 1 + w ≠ 0 := by
    intro h; apply hw; linear_combination h
  have hx' : (x₂ : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  have h2 : (x₂ : ℂ) - x₂ * w / (1 + w) = x₂ / (1 + w) := by field_simp; ring
  simp only [targetChange, targetChangeInv, h2]
  field_simp

/-- The imaginary part of `ψ(z)`: `Im ψ(z) = x₂ Im z / |x₂ − z|²`. -/
theorem im_targetChange (x₂ : ℝ) (z : ℂ) :
    (targetChange x₂ z).im = x₂ * z.im / normSq ((x₂ : ℂ) - z) := by
  simp only [targetChange, div_im, sub_re, ofReal_re, sub_im, ofReal_im]
  ring

/-- The imaginary part of `ψ⁻¹(w)`: `Im ψ⁻¹(w) = x₂ Im w / |1 + w|²`. -/
theorem im_targetChangeInv (x₂ : ℝ) (w : ℂ) :
    (targetChangeInv x₂ w).im = x₂ * w.im / normSq (1 + w) := by
  simp only [targetChangeInv, div_im, mul_re, mul_im, ofReal_re, ofReal_im, add_re, add_im, one_re,
    one_im]
  ring

theorem targetChange_mem_H (hx : 0 < x₂) {z : ℂ} (hz : z ∈ H) : targetChange x₂ z ∈ H := by
  have hz' : 0 < z.im := hz
  have hne : (x₂ : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  show 0 < (targetChange x₂ z).im
  rw [im_targetChange]
  exact div_pos (mul_pos hx hz') (normSq_pos.2 hne)

theorem targetChangeInv_mem_H (hx : 0 < x₂) {w : ℂ} (hw : w ∈ H) : targetChangeInv x₂ w ∈ H := by
  have hw' : 0 < w.im := hw
  have hne : 1 + w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  show 0 < (targetChangeInv x₂ w).im
  rw [im_targetChangeInv]
  exact div_pos (mul_pos hx hw') (normSq_pos.2 hne)

theorem ne_ofReal_of_mem_H {z : ℂ} (hz : z ∈ H) (x : ℝ) : z ≠ x := by
  intro h
  have : z.im = 0 := by rw [h]; simp
  have hz' : 0 < z.im := hz
  linarith

/-- (C1): `ψ` maps the upper half-plane bijectively onto itself. -/
theorem bijOn_targetChange_H (hx : 0 < x₂) : BijOn (targetChange x₂) H H := by
  refine ⟨fun z hz => targetChange_mem_H hx hz, ?_, ?_⟩
  · intro z hz z' hz' h
    have := congrArg (targetChangeInv x₂) h
    rwa [targetChangeInv_targetChange hx.ne' (ne_ofReal_of_mem_H hz x₂),
      targetChangeInv_targetChange hx.ne' (ne_ofReal_of_mem_H hz' x₂)] at this
  · intro w hw
    refine ⟨targetChangeInv x₂ w, targetChangeInv_mem_H hx hw, ?_⟩
    have : w ≠ ((-1 : ℝ) : ℂ) := ne_ofReal_of_mem_H hw (-1)
    exact targetChange_targetChangeInv hx.ne' (by simpa using this)

/-- (C1): the old target `∞` goes to `−1`. -/
theorem tendsto_targetChange_cobounded (x₂ : ℝ) :
    Tendsto (targetChange x₂) (cobounded ℂ) (𝓝 (-1)) := by
  -- `ψ(z) = −1 + x₂ (x₂ − z)⁻¹`
  have hform : ∀ z : ℂ, z ≠ x₂ → targetChange x₂ z = -1 + x₂ * ((x₂ : ℂ) - z)⁻¹ := by
    intro z hz
    have h1 : (x₂ : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    simp only [targetChange]
    field_simp
    ring
  have hlim : Tendsto (fun z : ℂ => -1 + x₂ * ((x₂ : ℂ) - z)⁻¹) (cobounded ℂ) (𝓝 (-1)) := by
    have h0 : Tendsto (fun z : ℂ => ((x₂ : ℂ) - z)⁻¹) (cobounded ℂ) (𝓝 0) :=
      tendsto_inv₀_cobounded.comp (tendsto_const_sub_cobounded _)
    simpa using (tendsto_const_nhds (x := (-1 : ℂ))).add (h0.const_mul (x₂ : ℂ))
  refine hlim.congr' ?_
  have hb : {z : ℂ | z ≠ x₂} ∈ cobounded ℂ := by
    rw [← isCobounded_def, ← isBounded_compl_iff]
    have : {z : ℂ | z ≠ x₂}ᶜ = {(x₂ : ℂ)} := by ext z; simp
    rw [this]; exact isBounded_singleton
  filter_upwards [hb] with z hz
  exact (hform z hz).symm

/-- (C1): the new target is `x₂`: `|ψ(z)| → ∞` as `z → x₂`. -/
theorem tendsto_norm_targetChange_nhdsNE (x₂ : ℝ) (hx : x₂ ≠ 0) :
    Tendsto (fun z => ‖targetChange x₂ z‖) (𝓝[≠] (x₂ : ℂ)) atTop := by
  have hsub : Tendsto (fun z : ℂ => (x₂ : ℂ) - z) (𝓝[≠] (x₂ : ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => (x₂ : ℂ) - z) (𝓝 (x₂ : ℂ)) (𝓝 ((x₂ : ℂ) - x₂)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.2 (Ne.symm hz)
  have hinv : Tendsto (fun z : ℂ => ‖((x₂ : ℂ) - z)⁻¹‖) (𝓝[≠] (x₂ : ℂ)) atTop :=
    tendsto_norm_inv_nhdsNE_zero_atTop.comp hsub
  have hnum : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (x₂ : ℂ)) (𝓝 ‖(x₂ : ℂ)‖) :=
    (continuous_norm.tendsto _).mono_left nhdsWithin_le_nhds
  have hpos : 0 < ‖(x₂ : ℂ)‖ := norm_pos_iff.2 (ofReal_ne_zero.2 hx)
  have := Tendsto.pos_mul_atTop hpos hnum hinv
  refine this.congr' (Eventually.of_forall fun z => ?_)
  simp only [targetChange, div_eq_mul_inv, norm_mul]

/-- The pole of `ψ⁻¹`: a transformed point tending to `−1` (the old target) has original image tending to `∞`. -/
theorem tendsto_targetChangeInv_nhdsNE_neg_one (hx : x₂ ≠ 0) :
    Tendsto (targetChangeInv x₂) (𝓝[≠] (-1 : ℂ)) (cobounded ℂ) := by
  -- `ψ⁻¹(w) = x₂ − x₂ (1 + w)⁻¹`
  have hform : ∀ w : ℂ, w ≠ -1 → targetChangeInv x₂ w = x₂ - x₂ * (1 + w)⁻¹ := by
    intro w hw
    have h1 : 1 + w ≠ 0 := by intro h; apply hw; linear_combination h
    simp only [targetChangeInv]
    field_simp
    ring
  have hadd : Tendsto (fun w : ℂ => 1 + w) (𝓝[≠] (-1 : ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun w : ℂ => 1 + w) (𝓝 (-1 : ℂ)) (𝓝 (1 + -1)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_neg_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h; apply hw; show w = -1; linear_combination (Set.mem_singleton_iff.1 h)
  have hinv : Tendsto (fun w : ℂ => (1 + w)⁻¹) (𝓝[≠] (-1 : ℂ)) (cobounded ℂ) :=
    tendsto_inv₀_nhdsNE_zero.comp hadd
  have hmul : Tendsto (fun w : ℂ => (x₂ : ℂ) * (1 + w)⁻¹) (𝓝[≠] (-1 : ℂ)) (cobounded ℂ) := by
    have hx' : (x₂ : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
    rw [← tendsto_norm_atTop_iff_cobounded] at hinv ⊢
    simp only [norm_mul]
    exact hinv.const_mul_atTop (norm_pos_iff.2 hx')
  have hsub : Tendsto (fun w : ℂ => (x₂ : ℂ) - x₂ * (1 + w)⁻¹) (𝓝[≠] (-1 : ℂ)) (cobounded ℂ) :=
    (tendsto_const_sub_cobounded _).comp hmul
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (hform w hw).symm


/-! ### The target change on the real line -/

/-- `ψ` on the real line, `x ↦ x / (x₂ − x)`. -/
def targetChangeReal (x₂ x : ℝ) : ℝ := x / (x₂ - x)

/-- `ψ⁻¹` on the real line, `q ↦ x₂ q / (1 + q)`. -/
def targetChangeInvReal (x₂ q : ℝ) : ℝ := x₂ * q / (1 + q)

theorem targetChange_ofReal (x₂ x : ℝ) : targetChange x₂ x = (targetChangeReal x₂ x : ℂ) := by
  simp [targetChange, targetChangeReal]

theorem targetChangeInv_ofReal (x₂ q : ℝ) :
    targetChangeInv x₂ q = (targetChangeInvReal x₂ q : ℂ) := by
  simp [targetChangeInv, targetChangeInvReal]

@[simp] theorem targetChangeReal_zero (x₂ : ℝ) : targetChangeReal x₂ 0 = 0 := by
  simp [targetChangeReal]

theorem targetChangeReal_eq_zero_iff {x : ℝ} (hx : x < x₂) : targetChangeReal x₂ x = 0 ↔ x = 0 := by
  rw [targetChangeReal, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact h
    · linarith
  · exact fun h => Or.inl h

theorem targetChangeInvReal_targetChangeReal (hx : x₂ ≠ 0) {x : ℝ} (hxx : x ≠ x₂) :
    targetChangeInvReal x₂ (targetChangeReal x₂ x) = x := by
  have := targetChangeInv_targetChange hx (z := (x : ℂ)) (by exact_mod_cast hxx)
  rw [targetChange_ofReal, targetChangeInv_ofReal] at this
  exact_mod_cast this

theorem targetChangeReal_targetChangeInvReal (hx : x₂ ≠ 0) {q : ℝ} (hq : q ≠ -1) :
    targetChangeReal x₂ (targetChangeInvReal x₂ q) = q := by
  have := targetChange_targetChangeInv hx (w := (q : ℂ)) (by exact_mod_cast hq)
  rw [targetChangeInv_ofReal, targetChange_ofReal] at this
  exact_mod_cast this

/-- `ψ(x) − ψ(y) = x₂ (x − y) / ((x₂ − x)(x₂ − y))`. -/
theorem targetChangeReal_sub (x₂ : ℝ) {x y : ℝ} (hx : x ≠ x₂) (hy : y ≠ x₂) :
    targetChangeReal x₂ x - targetChangeReal x₂ y = x₂ * (x - y) / ((x₂ - x) * (x₂ - y)) := by
  have h1 : x₂ - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have h2 : x₂ - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  simp only [targetChangeReal]
  field_simp
  ring

/-- `ψ` is strictly increasing on `(−∞, x₂)`. -/
theorem strictMonoOn_targetChangeReal_Iio (hx : 0 < x₂) : StrictMonoOn (targetChangeReal x₂) (Iio x₂) := by
  intro x hx' y hy' hxy
  have h := targetChangeReal_sub x₂ (ne_of_lt (mem_Iio.1 hy')) (ne_of_lt (mem_Iio.1 hx'))
  have h1 : 0 < x₂ - x := sub_pos.2 hx'
  have h2 : 0 < x₂ - y := sub_pos.2 hy'
  have : 0 < targetChangeReal x₂ y - targetChangeReal x₂ x := by
    rw [h]; exact div_pos (mul_pos hx (sub_pos.2 hxy)) (mul_pos h2 h1)
  linarith

/-- `ψ` is strictly increasing on `(x₂, ∞)`. -/
theorem strictMonoOn_targetChangeReal_Ioi (hx : 0 < x₂) : StrictMonoOn (targetChangeReal x₂) (Ioi x₂) := by
  intro x hx' y hy' hxy
  have hx'' : x₂ < x := hx'
  have hy'' : x₂ < y := hy'
  have h := targetChangeReal_sub x₂ (ne_of_gt hy'') (ne_of_gt hx'')
  have h1 : x₂ - x < 0 := sub_neg.2 hx''
  have h2 : x₂ - y < 0 := sub_neg.2 hy''
  have : 0 < targetChangeReal x₂ y - targetChangeReal x₂ x := by
    rw [h]; exact div_pos (mul_pos hx (sub_pos.2 hxy)) (mul_pos_of_neg_of_neg h2 h1)
  linarith

/-- The marks `0 ≤ x < x₂` before the new target stay on the right: `ψ(x) ≥ 0`. -/
theorem targetChangeReal_nonneg {x : ℝ} (h0 : 0 ≤ x) (hx : x < x₂) : 0 ≤ targetChangeReal x₂ x :=
  div_nonneg h0 (sub_pos.2 hx).le

/-- The marks after the new target go to the left of the old target: `ψ(x) < −1` for `x > x₂ > 0`. -/
theorem targetChangeReal_lt_neg_one (hx : 0 < x₂) {x : ℝ} (hxx : x₂ < x) : targetChangeReal x₂ x < -1 := by
  have h1 : x₂ - x < 0 := sub_neg.2 hxx
  rw [targetChangeReal, div_lt_iff_of_neg h1]
  linarith

/-- Points before the new target stay to the right of the old target: `−1 < ψ(x)` for `x < x₂`, `0 < x₂`. -/
theorem neg_one_lt_targetChangeReal (hx : 0 < x₂) {x : ℝ} (hxx : x < x₂) : -1 < targetChangeReal x₂ x := by
  have h1 : 0 < x₂ - x := sub_pos.2 hxx
  rw [targetChangeReal, lt_div_iff₀ h1]
  linarith

/-- A transformed swallowing point `q < −1` beyond the old target pulls back beyond the new target:
`ψ⁻¹(q) > x₂` ((C2) ff., "If `q < −1`, then `ψ⁻¹(q) > x₂`"). -/
theorem lt_targetChangeInvReal (hx : 0 < x₂) {q : ℝ} (hq : q < -1) : x₂ < targetChangeInvReal x₂ q := by
  have h1 : 1 + q < 0 := by linarith
  rw [targetChangeInvReal, lt_div_iff_of_neg h1]
  nlinarith

/-- Conversely `ψ⁻¹(q) ∈ (−∞, x₂)` is impossible for `q < −1`, and a point `q > −1` pulls back below `x₂`. -/
theorem targetChangeInvReal_lt (hx : 0 < x₂) {q : ℝ} (hq : -1 < q) : targetChangeInvReal x₂ q < x₂ := by
  have h1 : 0 < 1 + q := by linarith
  rw [targetChangeInvReal, div_lt_iff₀ h1]
  nlinarith

/-! ### The transformed force word (C2) -/

/-- (C2), positions of the transformed left marks, nearest the seed first: the old target `−1`, then
`ψ(x_N), ψ(x_{N−1}), …, ψ(x₃)`. Here `N = n + 2` and the original right marks are `xR : Fin (n + 2) → ℝ`
(Lean index `j` is the source index `j + 1`). -/
def targetChangePosL {n : ℕ} (xR : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (-1) fun i : Fin n => targetChangeReal (xR 1) (xR (Fin.rev i.castSucc.castSucc))

/-- (C2), weights of the transformed left marks: the old target has weight `κ − 6 − S_N`, and the mark
`ψ(x_j)` keeps the weight `ρ_j`. -/
def targetChangeWeightL (κ : ℝ) {n : ℕ} (ρR : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (κ - 6 - ∑ j, ρR j) fun i : Fin n => ρR (Fin.rev i.castSucc.castSucc)

/-- (C2), the sole transformed right mark `ψ(x₁)`. -/
def targetChangePosR {n : ℕ} (xR : Fin (n + 2) → ℝ) : Fin 1 → ℝ :=
  fun _ => targetChangeReal (xR 1) (xR 0)

/-- (C2), its weight `ρ₁`. -/
def targetChangeWeightR {n : ℕ} (ρR : Fin (n + 2) → ℝ) : Fin 1 → ℝ :=
  fun _ => ρR 0

/-- The reversed index `Fin.rev i.castSucc.castSucc` (source index `N − i`, Lean `n + 1 − i`) is at least
`2` (source index `≥ 3`). -/
theorem two_le_rev_castSucc_castSucc {n : ℕ} (i : Fin n) : 2 ≤ ((Fin.rev i.castSucc.castSucc : Fin (n + 2)) : ℕ) := by
  simp only [Fin.val_rev, Fin.val_castSucc]
  omega

/-- There are exactly `N` finite groups after the target change (an existing mark became the target). -/
theorem targetChange_card (n : ℕ) : (n + 1) + 1 = n + 2 := rfl

/-- (C2): with `0 ≤ x₁ < x₂ < ⋯ < x_N`, the transformed left positions are strictly decreasing away from the
seed: `−1 > ψ(x_N) > ⋯ > ψ(x₃)`. -/
theorem strictAnti_targetChangePosL {n : ℕ} {xR : Fin (n + 2) → ℝ} (hmono : StrictMono xR) (h0 : 0 ≤ xR 0) :
    StrictAnti (targetChangePosL xR) := by
  have hx2 : 0 < xR 1 := lt_of_le_of_lt h0 (hmono (show (0 : Fin (n + 2)) < 1 by
    rw [Fin.lt_def]; simp))
  have hgt : ∀ i : Fin n, xR 1 < xR (Fin.rev i.castSucc.castSucc) := by
    intro i
    apply hmono
    rw [Fin.lt_def]
    have := two_le_rev_castSucc_castSucc i
    simp only [Fin.val_one] at *
    omega
  have key : ∀ a b : Fin (n + 1), a < b → targetChangePosL xR b < targetChangePosL xR a := by
    intro a b hab
    induction b using Fin.cases with
    | zero => exact absurd hab (Fin.not_lt_zero a)
    | succ j =>
      induction a using Fin.cases with
      | zero =>
        simp only [targetChangePosL, Fin.cons_zero, Fin.cons_succ]
        exact targetChangeReal_lt_neg_one hx2 (hgt j)
      | succ i =>
        simp only [targetChangePosL, Fin.cons_succ]
        have hij : i < j := Fin.succ_lt_succ_iff.1 hab
        apply strictMonoOn_targetChangeReal_Ioi hx2 (hgt j) (hgt i)
        apply hmono
        rw [Fin.lt_def]
        simp only [Fin.val_rev, Fin.val_castSucc]
        have := Fin.lt_def.1 hij
        omega
  exact fun a b hab => key a b hab

/-- (C2): every transformed left mark is at most `−1 < 0`. -/
theorem targetChangePosL_le_neg_one {n : ℕ} {xR : Fin (n + 2) → ℝ} (hmono : StrictMono xR) (h0 : 0 ≤ xR 0)
    (i : Fin (n + 1)) : targetChangePosL xR i ≤ -1 := by
  have := (strictAnti_targetChangePosL hmono h0).antitone (Fin.zero_le i)
  simpa [targetChangePosL] using this

/-- (C2): the transformed word is an ordered force word (left marks `≤ 0` in decreasing order, the right mark
`ψ(x₁) ≥ 0`). -/
theorem isOrderedForceWord_targetChange {n : ℕ} {xR : Fin (n + 2) → ℝ} (hmono : StrictMono xR)
    (h0 : 0 ≤ xR 0) : IsOrderedForceWord (targetChangePosL xR) (targetChangePosR xR) := by
  have hx01 : xR 0 < xR 1 := hmono (show (0 : Fin (n + 2)) < 1 by rw [Fin.lt_def]; simp)
  refine ⟨(strictAnti_targetChangePosL hmono h0).antitone, fun i => ?_, ?_, fun _ => ?_⟩
  · linarith [targetChangePosL_le_neg_one hmono h0 i]
  · intro a b _; rfl
  · exact targetChangeReal_nonneg h0 hx01

/-- (C2): the sole right mark is at `0⁺` exactly when the first original group is at the seed. -/
theorem targetChangePosR_eq_zero_iff {n : ℕ} {xR : Fin (n + 2) → ℝ} (hmono : StrictMono xR) (i : Fin 1) :
    targetChangePosR xR i = 0 ↔ xR 0 = 0 :=
  targetChangeReal_eq_zero_iff (hmono (show (0 : Fin (n + 2)) < 1 by rw [Fin.lt_def]; simp))

/-- `∑_{j ≥ 2} ρ_j` (source indices `3, …, N`) written as the reversed sum used in (C2). -/
theorem sum_rev_castSucc_castSucc {n : ℕ} (ρR : Fin (n + 2) → ℝ) :
    ∑ i : Fin n, ρR (Fin.rev i.castSucc.castSucc) = ∑ j, ρR j - (ρR 0 + ρR 1) := by
  have hrev : ∑ j : Fin (n + 2), ρR j = ∑ j : Fin (n + 2), ρR (Fin.rev j) :=
    (Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)).symm
  rw [hrev, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.rev_castSucc, Fin.rev_last, Fin.succ_zero_eq_one]
  ring

/-- (C2): the transformed left total is `κ − 6 − S₂`. -/
theorem sum_targetChangeWeightL (κ : ℝ) {n : ℕ} (ρR : Fin (n + 2) → ℝ) :
    ∑ i, targetChangeWeightL κ ρR i = κ - 6 - (ρR 0 + ρR 1) := by
  rw [Fin.sum_univ_succ]
  simp only [targetChangeWeightL, Fin.cons_zero, Fin.cons_succ]
  rw [sum_rev_castSucc_castSucc]
  ring

/-- (C2): the transformed right total is `ρ₁`. -/
theorem sum_targetChangeWeightR {n : ℕ} (ρR : Fin (n + 2) → ℝ) :
    ∑ i, targetChangeWeightR ρR i = ρR 0 := by
  simp [targetChangeWeightR]

/-- For `N = 2` the transformed left list consists only of the old target `−1`, of weight `κ − 6 − S₂`. -/
theorem targetChangePosL_two (xR : Fin 2 → ℝ) (i : Fin 1) : targetChangePosL (n := 0) xR i = -1 := by
  rw [Fin.fin_one_eq_zero i]; rfl

theorem targetChangeWeightL_two (κ : ℝ) (ρR : Fin 2 → ℝ) (i : Fin 1) :
    targetChangeWeightL κ (n := 0) ρR i = κ - 6 - (ρR 0 + ρR 1) := by
  rw [Fin.fin_one_eq_zero i]
  simp [targetChangeWeightL, Fin.sum_univ_two]

/-- `ψ⁻¹` maps every transformed mark back to the original mark it came from: the right mark to `x₁`, and the left
mark `ψ(x_j)` (`j ≥ 3`) to `x_j`. -/
theorem targetChangeInvReal_targetChangePosR {n : ℕ} {xR : Fin (n + 2) → ℝ} (hmono : StrictMono xR)
    (h0 : 0 ≤ xR 0) (i : Fin 1) : targetChangeInvReal (xR 1) (targetChangePosR xR i) = xR 0 := by
  have hx01 : xR 0 < xR 1 := hmono (show (0 : Fin (n + 2)) < 1 by rw [Fin.lt_def]; simp)
  exact targetChangeInvReal_targetChangeReal (by linarith) hx01.ne

theorem targetChangeInvReal_targetChangePosL_succ {n : ℕ} {xR : Fin (n + 2) → ℝ} (hmono : StrictMono xR)
    (h0 : 0 ≤ xR 0) (i : Fin n) :
    targetChangeInvReal (xR 1) (targetChangePosL xR i.succ) = xR (Fin.rev i.castSucc.castSucc) := by
  have hx01 : xR 0 < xR 1 := hmono (show (0 : Fin (n + 2)) < 1 by rw [Fin.lt_def]; simp)
  have hgt : xR 1 < xR (Fin.rev i.castSucc.castSucc) := by
    apply hmono
    rw [Fin.lt_def]
    have := two_le_rev_castSucc_castSucc i
    simp only [Fin.val_one] at *
    omega
  simp only [targetChangePosL, Fin.cons_succ]
  exact targetChangeInvReal_targetChangeReal (by linarith) hgt.ne'

end Sec7

end InteractingSLE
