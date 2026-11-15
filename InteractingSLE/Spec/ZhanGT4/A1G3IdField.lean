/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3IdStoch

/-!
# Zhan's A.1 (G3): the logarithm of the inverse `SLE_κ(κ − 4, −4)` martingale as a drifted log-field

Packet PROVE-A1-G3ROW2. Source: the specification's force-point martingale (proof of Theorem 2.2, L488; Lemma 2.1's
`SLE_κ(ρ)` density) and Astra, *Follow-up proofs*, §A.1.3 (the Girsanov removal of the own drift).

The large (G3) curve is `SLE_κ(κ − 4, −4)`: `W = √κ B + D` with `D' = (κ − 4)/(W − V₀) − 4/(W − V₁)` and force points
`V_i' = 2/(V_i − W)`. The field (in the driver position `x`)

`ℓ(t, x) = ∫₀ᵗ 2/(V₁ − W)² + (4/κ) log(x − V₁) − ((κ − 4)/κ) log(x − V₀) + (8/κ − 2) ∫₀ᵗ 2/((V₀ − W)(V₁ − W))`

is the logarithm of the inverse martingale ratio `M_0/M_t` (at `x = W_t`, up to a constant), written with the pair
term in its integrated form (`sub_eq_mul_exp_of_force`). This file defines `ℓ`, its space derivatives `ℓ_x`, `ℓ_xx`,
`ℓ_xxx`, its time derivative `ℓ_t`, the drift `b`, and proves the pathwise facts: the force points' derivatives on
`[0, S]`, the drift's derivative, the space derivatives off the force points, the time derivative, and the drifted
generator identity `ℓ_t + b ℓ_x + (κ/2)(ℓ_xx + ℓ_x²) = 0` at the driver.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Id

namespace G3Field

variable {Ω : Type*} (κ : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 2 → ℝ≥0 → Ω → ℝ)

/-- The weight of `log(x − V₁)` in `−log M`: `4/κ`. -/
def cy : ℝ := -(4 / κ)

/-- The weight of `log(x − V₀)` in `log M`: `(κ − 4)/κ`. -/
def cx : ℝ := (κ - 4) / κ

/-- The weight of `log(V₀ − V₁)` in `log M`: `8/κ − 2`. -/
def cxy : ℝ := 8 / κ - 2

/-- The driver at a real time. -/
def w (ω : Ω) : ℝ → ℝ := Strip.extPath (W · ω)

/-- The force points at a real time. -/
def v (i : Fin 2) (ω : Ω) : ℝ → ℝ := Strip.extPath (VL i · ω)

/-- `∫₀ᵗ 2/(V₁ − W)²` (`−log g_t'(y)`). -/
def I1 (ω : Ω) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, 2 / (v VL 1 ω s - w W ω s) ^ 2

/-- `∫₀ᵗ 2/((V₀ − W)(V₁ − W))` (`log(x − y) − log(V₀ − V₁)`). -/
def I2 (ω : Ω) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, 2 / ((v VL 0 ω s - w W ω s) * (v VL 1 ω s - w W ω s))

/-- **The field** `ℓ(t, x)`. -/
def ell (ω : Ω) (t x : ℝ) : ℝ :=
  I1 W VL ω t - cy κ * Real.log (x - v VL 1 ω t) - cx κ * Real.log (x - v VL 0 ω t) + cxy κ * I2 W VL ω t

/-- `∂_x ℓ`. -/
def ellX (ω : Ω) (t x : ℝ) : ℝ := -cy κ / (x - v VL 1 ω t) - cx κ / (x - v VL 0 ω t)

/-- `∂²_x ℓ`. -/
def ellXX (ω : Ω) (t x : ℝ) : ℝ := cy κ / (x - v VL 1 ω t) ^ 2 + cx κ / (x - v VL 0 ω t) ^ 2

/-- `∂³_x ℓ`. -/
def ellXXX (ω : Ω) (t x : ℝ) : ℝ := -(2 * cy κ) / (x - v VL 1 ω t) ^ 3 - 2 * cx κ / (x - v VL 0 ω t) ^ 3

/-- `∂_t ℓ` at a fixed `x`. -/
def ellT (ω : Ω) (t x : ℝ) : ℝ :=
  2 / (v VL 1 ω t - w W ω t) ^ 2 + cy κ * (2 / (v VL 1 ω t - w W ω t)) / (x - v VL 1 ω t) +
    cx κ * (2 / (v VL 0 ω t - w W ω t)) / (x - v VL 0 ω t) +
      cxy κ * (2 / ((v VL 0 ω t - w W ω t) * (v VL 1 ω t - w W ω t)))

/-- **The drift** `b = (κ − 4)/(W − V₀) − 4/(W − V₁)`. -/
def drift (ω : Ω) (t : ℝ) : ℝ := (κ - 4) / (w W ω t - v VL 0 ω t) + -4 / (w W ω t - v VL 1 ω t)

/-- The finite-variation part `D = W − √κ B`. -/
def D (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun u ω => W u ω - Real.sqrt κ * B u ω

variable {κ W VL}

theorem driftDriver_eq (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) :
    driftDriver (Real.sqrt κ) B (D κ W B) ω t = w W ω t := by
  simp only [driftDriver, D, w, Strip.extPath]
  ring

/-! ### Algebra -/

/-- **The drifted generator vanishes at the driver**: `ℓ_t + b ℓ_x + (κ/2)(ℓ_xx + ℓ_x²) = 0` at `x = W_t`. -/
theorem gen_eq_zero (hκ : 0 < κ) (ω : Ω) (t : ℝ) (h0 : w W ω t - v VL 0 ω t ≠ 0) (h1 : w W ω t - v VL 1 ω t ≠ 0) :
    ellT κ W VL ω t (w W ω t) + drift κ W VL ω t * ellX κ VL ω t (w W ω t) +
      Real.sqrt κ ^ 2 / 2 * (ellXX κ VL ω t (w W ω t) + ellX κ VL ω t (w W ω t) ^ 2) = 0 := by
  have h0' : v VL 0 ω t - w W ω t ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 h0
  have h1' : v VL 1 ω t - w W ω t ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 h1
  have hκ0 : κ ≠ 0 := hκ.ne'
  rw [Real.sq_sqrt hκ.le]
  simp only [ellT, drift, ellX, ellXX, cy, cx, cxy]
  field_simp
  ring

/-! ### Space derivatives -/

theorem hasDerivAt_ell (ω : Ω) (t x : ℝ) (h0 : x - v VL 0 ω t ≠ 0) (h1 : x - v VL 1 ω t ≠ 0) :
    HasDerivAt (ell κ W VL ω t) (ellX κ VL ω t x) x := by
  have d1 := ((hasDerivAt_id x).sub_const (v VL 1 ω t)).log h1
  have d0 := ((hasDerivAt_id x).sub_const (v VL 0 ω t)).log h0
  have h := (((hasDerivAt_const x (I1 W VL ω t)).sub (d1.const_mul (cy κ))).sub (d0.const_mul (cx κ))).add
    (hasDerivAt_const x (cxy κ * I2 W VL ω t))
  refine h.congr_deriv ?_
  simp only [ellX, id]
  field_simp
  ring

theorem hasDerivAt_ellX (ω : Ω) (t x : ℝ) (h0 : x - v VL 0 ω t ≠ 0) (h1 : x - v VL 1 ω t ≠ 0) :
    HasDerivAt (ellX κ VL ω t) (ellXX κ VL ω t x) x := by
  have d1 := (hasDerivAt_const x (-cy κ)).div ((hasDerivAt_id x).sub_const (v VL 1 ω t)) h1
  have d0 := (hasDerivAt_const x (cx κ)).div ((hasDerivAt_id x).sub_const (v VL 0 ω t)) h0
  refine (d1.sub d0).congr_deriv ?_
  simp only [ellXX, id]
  field_simp
  ring

theorem hasDerivAt_ellXX (ω : Ω) (t x : ℝ) (h0 : x - v VL 0 ω t ≠ 0) (h1 : x - v VL 1 ω t ≠ 0) :
    HasDerivAt (ellXX κ VL ω t) (ellXXX κ VL ω t x) x := by
  have d1 := (hasDerivAt_const x (cy κ)).div (((hasDerivAt_id x).sub_const (v VL 1 ω t)).pow 2)
    (pow_ne_zero 2 h1)
  have d0 := (hasDerivAt_const x (cx κ)).div (((hasDerivAt_id x).sub_const (v VL 0 ω t)).pow 2)
    (pow_ne_zero 2 h0)
  refine (d1.add d0).congr_deriv ?_
  simp only [ellXXX, id, Pi.pow_apply]
  field_simp
  ring

/-! ### Pathwise facts on `[0, S]` -/

section Path

variable {xL : Fin 2 → ℝ} {xR ρR : Fin 0 → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {ω : Ω} {S : ℝ≥0} {δ : ℝ}

/-- The path hypotheses of one sample on `[0, S]`: the large `SLE_κ(κ − 4, −4)` path relation, `S` before the
lifetime, and the force gaps at least `δ` up to `S`. -/
structure PathOn (κ : ℝ) (xL : Fin 2 → ℝ) (xR ρR : Fin 0 → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 2 → ℝ≥0 → Ω → ℝ)
    (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) (S : ℝ≥0) (δ : ℝ) : Prop where
  path : IsIntegratedSLEPath κ xL xR ![κ - 4, -4] ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω)
    (ζ ω)
  lt : (S : ℝ≥0∞) < ζ ω
  pos : 0 < δ
  gap : ∀ r ≤ S, ∀ i, δ ≤ |W r ω - VL i r ω|

namespace PathOn

variable (h : PathOn κ xL xR ρR W VL VR B ζ ω S δ)
include h

theorem lt' : ENNReal.ofReal (S : ℝ) < ζ ω := by rw [ENNReal.ofReal_coe_nnreal]; exact h.lt

theorem contW : ContinuousOn (w W ω) (Icc 0 (S : ℝ)) :=
  A1Ref.continuousOn_extPath_Icc h.path.2.2.2.1 h.lt'

theorem contV (i : Fin 2) : ContinuousOn (v VL i ω) (Icc 0 (S : ℝ)) :=
  A1Ref.continuousOn_extPath_Icc (h.path.2.2.2.2.1 i) h.lt'

omit h in
theorem toNNReal_le {u : ℝ} (hu : u ∈ Icc (0 : ℝ) S) : u.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hu.2

theorem gap' {u : ℝ} (hu : u ∈ Icc (0 : ℝ) S) (i : Fin 2) : δ ≤ |w W ω u - v VL i ω u| :=
  h.gap _ (toNNReal_le hu) i

theorem ne {u : ℝ} (hu : u ∈ Icc (0 : ℝ) S) (i : Fin 2) : w W ω u - v VL i ω u ≠ 0 := fun he => by
  have := h.gap' hu i
  rw [he, abs_zero] at this
  exact absurd this (not_le.2 h.pos)

theorem ne' {u : ℝ} (hu : u ∈ Icc (0 : ℝ) S) (i : Fin 2) : v VL i ω u - w W ω u ≠ 0 := by
  rw [← neg_sub]; exact neg_ne_zero.2 (h.ne hu i)

theorem lt_of_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) S) : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω :=
  lt_of_le_of_lt (ENNReal.coe_le_coe.2 (toNNReal_le hu)) h.lt

/-- **The force points' derivative on `[0, S]`**: `V_i' = 2/(V_i − W)` within `[0, S]`. -/
theorem hasDerivWithinAt_v (i : Fin 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    HasDerivWithinAt (v VL i ω) (2 / (v VL i ω t - w W ω t)) (Icc 0 (S : ℝ)) t := by
  have hg : ContinuousOn (fun s => 2 / (v VL i ω s - w W ω s)) (Icc 0 (S : ℝ)) :=
    continuousOn_const.div ((h.contV i).sub h.contW) fun u hu => h.ne' hu i
  have he : ∀ u ∈ Icc (0 : ℝ) S, v VL i ω u = xL i + ∫ s in (0 : ℝ)..u, 2 / (v VL i ω s - w W ω s) := by
    intro u hu
    have := h.path.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (h.lt_of_mem hu) i
    simp only [v, w, Strip.extPath] at this ⊢
    rw [this, Real.coe_toNNReal _ hu.1]
  exact ((hasDerivWithinAt_integral_base_real hg ht).const_add (xL i)).congr (fun u hu => he u hu) (he t ht)

/-- **The drift's derivative on `[0, S]`**: `D = W − √κ B` has derivative `b` within `[0, S]`. -/
theorem hasDerivWithinAt_D {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    HasDerivWithinAt (fun s : ℝ => D κ W B s.toNNReal ω) (drift κ W VL ω t) (Icc 0 (S : ℝ)) t := by
  have hg : ∀ i : Fin 2, ContinuousOn (fun s => (![κ - 4, -4] : Fin 2 → ℝ) i / (w W ω s - v VL i ω s))
      (Icc 0 (S : ℝ)) := fun i =>
    continuousOn_const.div (h.contW.sub (h.contV i)) fun u hu => h.ne hu i
  have he : ∀ u ∈ Icc (0 : ℝ) S, D κ W B u.toNNReal ω =
      (∫ s in (0 : ℝ)..u, (κ - 4) / (w W ω s - v VL 0 ω s)) + ∫ s in (0 : ℝ)..u, -4 / (w W ω s - v VL 1 ω s) := by
    intro u hu
    have := h.path.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (h.lt_of_mem hu)
    simp only [Fin.sum_univ_two, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.coe_toNNReal _ hu.1] at this
    simp only [D, v, w, Strip.extPath]
    rw [this]
    ring
  have d0 := hasDerivWithinAt_integral_base_real (hg 0) ht
  have d1 := hasDerivWithinAt_integral_base_real (hg 1) ht
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at d0 d1
  exact (d0.add d1).congr (fun u hu => he u hu) (he t ht)

/-- **The time derivative of the field at a fixed position** off the force points. -/
theorem hasDerivWithinAt_ell {t x : ℝ} (ht : t ∈ Icc (0 : ℝ) S) (h0 : x - v VL 0 ω t ≠ 0)
    (h1 : x - v VL 1 ω t ≠ 0) :
    HasDerivWithinAt (fun s => ell κ W VL ω s x) (ellT κ W VL ω t x) (Icc 0 (S : ℝ)) t := by
  have g1 : ContinuousOn (fun s => 2 / (v VL 1 ω s - w W ω s) ^ 2) (Icc 0 (S : ℝ)) :=
    continuousOn_const.div (((h.contV 1).sub h.contW).pow 2) fun u hu => pow_ne_zero 2 (h.ne' hu 1)
  have g2 : ContinuousOn (fun s => 2 / ((v VL 0 ω s - w W ω s) * (v VL 1 ω s - w W ω s))) (Icc 0 (S : ℝ)) :=
    continuousOn_const.div (((h.contV 0).sub h.contW).mul ((h.contV 1).sub h.contW)) fun u hu =>
      mul_ne_zero (h.ne' hu 0) (h.ne' hu 1)
  have dI1 := hasDerivWithinAt_integral_base_real g1 ht
  have dI2 := hasDerivWithinAt_integral_base_real g2 ht
  have dl1 := ((h.hasDerivWithinAt_v 1 ht).const_sub x).log h1
  have dl0 := ((h.hasDerivWithinAt_v 0 ht).const_sub x).log h0
  have hd := ((dI1.sub (dl1.const_mul (cy κ))).sub (dl0.const_mul (cx κ))).add (dI2.const_mul (cxy κ))
  refine hd.congr_deriv ?_
  simp only [ellT]
  ring

end PathOn

end Path

end G3Field

end InteractingSLE.ZhanGT4.A1G3Id
