/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3IdField

/-!
# Zhan's A.1 (G3): the inverse `SLE_κ(κ − 4, −4)` martingale's logarithm is a drifted log-field

Packet PROVE-A1-G3ROW2. A22's logarithmic Itô formula (`IsDriftLogField.seed_original_logIto`) applies to any field
`ℓ` that is regular and bounded on a tube around the driver `W = σB + D` over `[ε, S]`, whose drifted generator
vanishes at the driver and whose values along the driver are adapted (`IsDriftLogField`). Here this is verified for the
field `G3Field.ell` of the large G3 curve over `[0, S]`, for a stopping time `S` before the lifetime, bounded by `T`,
before which the force gaps are at least `δ` and at most `R` (tube radius `δ/2`):

* `abs_div_le_of_le`, `abs_div_pow_le_of_le`, `abs_log_le_of_le`: elementary bounds;
* `mem_tube`: on the tube, both force gaps lie in `[δ/2, R + δ/2]`;
* **`isDriftLogField_g3`**: `IsDriftLogField 𝓕 (√κ) (δ/8) K B D b 0 S ℓ ℓ_x ℓ_xx ℓ_xxx ℓ_t` for an explicit `K`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Id

namespace G3Field

/-! ### Elementary bounds -/

theorem abs_div_le_of_le {c u m : ℝ} (hm : 0 < m) (h : m ≤ |u|) : |c / u| ≤ |c| / m := by
  rw [abs_div]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hm h

theorem abs_div_pow_le_of_le {c u m : ℝ} (hm : 0 < m) (h : m ≤ |u|) (k : ℕ) : |c / u ^ k| ≤ |c| / m ^ k := by
  rw [abs_div, abs_pow]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hm k) (pow_le_pow_left₀ hm.le h k)

theorem abs_log_le_of_le {u m M : ℝ} (hm : 0 < m) (h1 : m ≤ |u|) (h2 : |u| ≤ M) :
    |Real.log u| ≤ |Real.log m| + |Real.log M| := by
  rw [← Real.log_abs]
  have hu : 0 < |u| := hm.trans_le h1
  have l1 : Real.log m ≤ Real.log |u| := Real.log_le_log hm h1
  have l2 : Real.log |u| ≤ Real.log M := Real.log_le_log hu h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)]
  · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]

theorem abs_div_mul_le_of_le {c u u' m : ℝ} (hm : 0 < m) (h : m ≤ |u|) (h' : m ≤ |u'|) :
    |c / (u * u')| ≤ |c| / m ^ 2 := by
  rw [abs_div, abs_mul]
  have hmm : m ^ 2 ≤ |u| * |u'| := by rw [sq]; exact mul_le_mul h h' hm.le (hm.le.trans h)
  exact div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hm 2) hmm

/-! ### The tube and the integrated terms -/

section Path

variable {Ω : Type*} {κ : ℝ} {xL : Fin 2 → ℝ} {xR ρR : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 2 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} {S : ℝ≥0} {δ R : ℝ}

/-- **On the tube of radius `δ/2` both force gaps lie in `[δ/2, R + δ/2]`.** -/
theorem mem_tube (h : PathOn κ xL xR ρR W VL VR B ζ ω S δ)
    (hR : ∀ r ≤ S, ∀ i, |W r ω - VL i r ω| ≤ R) {p : ℝ × ℝ}
    (hp : p ∈ driftTube (Real.sqrt κ) B (D κ W B) ((0 : ℝ≥0) : ℝ) S (4 * (δ / 8)) ω) :
    p.1 ∈ Icc (0 : ℝ) S ∧ ∀ i, δ / 2 ≤ |p.2 - v VL i ω p.1| ∧ |p.2 - v VL i ω p.1| ≤ R + δ / 2 := by
  obtain ⟨h1, h2⟩ := hp
  rw [NNReal.coe_zero] at h1
  rw [driftDriver_eq] at h2
  refine ⟨h1, fun i => ?_⟩
  have hg := h.gap' h1 i
  have hR' : |w W ω p.1 - v VL i ω p.1| ≤ R := hR _ (PathOn.toNNReal_le h1) i
  have e : p.2 - v VL i ω p.1 = (p.2 - w W ω p.1) + (w W ω p.1 - v VL i ω p.1) := by ring
  rw [e]
  constructor
  · have := abs_sub_abs_le_abs_sub (w W ω p.1 - v VL i ω p.1) (-(p.2 - w W ω p.1))
    rw [abs_neg] at this
    have e2 : w W ω p.1 - v VL i ω p.1 - -(p.2 - w W ω p.1) = p.2 - w W ω p.1 + (w W ω p.1 - v VL i ω p.1) := by
      ring
    rw [e2] at this
    linarith
  · exact (abs_add_le _ _).trans (by linarith)

theorem ne_of_mem_tube (h : PathOn κ xL xR ρR W VL VR B ζ ω S δ) (hR : ∀ r ≤ S, ∀ i, |W r ω - VL i r ω| ≤ R)
    {p : ℝ × ℝ} (hp : p ∈ driftTube (Real.sqrt κ) B (D κ W B) ((0 : ℝ≥0) : ℝ) S (4 * (δ / 8)) ω) (i : Fin 2) :
    p.2 - v VL i ω p.1 ≠ 0 := fun he => by
  have := ((mem_tube h hR hp).2 i).1
  rw [he, abs_zero] at this
  linarith [h.pos]

namespace PathOn

variable (h : PathOn κ xL xR ρR W VL VR B ζ ω S δ)
include h

theorem contI1' : ContinuousOn (fun s => 2 / (v VL 1 ω s - w W ω s) ^ 2) (Icc 0 (S : ℝ)) :=
  continuousOn_const.div (((h.contV 1).sub h.contW).pow 2) fun _ hu => pow_ne_zero 2 (h.ne' hu 1)

theorem contI2' : ContinuousOn (fun s => 2 / ((v VL 0 ω s - w W ω s) * (v VL 1 ω s - w W ω s))) (Icc 0 (S : ℝ)) :=
  continuousOn_const.div (((h.contV 0).sub h.contW).mul ((h.contV 1).sub h.contW)) fun _ hu =>
    mul_ne_zero (h.ne' hu 0) (h.ne' hu 1)

theorem contI1 : ContinuousOn (I1 W VL ω) (Icc 0 (S : ℝ)) := fun _ ht =>
  (hasDerivWithinAt_integral_base_real h.contI1' ht).continuousWithinAt

theorem contI2 : ContinuousOn (I2 W VL ω) (Icc 0 (S : ℝ)) := fun _ ht =>
  (hasDerivWithinAt_integral_base_real h.contI2' ht).continuousWithinAt

theorem abs_I1_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : |I1 W VL ω t| ≤ 2 / δ ^ 2 * t := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => 2 / (v VL 1 ω s - w W ω s) ^ 2) (C := 2 / δ ^ 2) fun s hs => by
      rw [uIoc_of_le ht.1] at hs
      have hsI : s ∈ Icc (0 : ℝ) S := ⟨hs.1.le, hs.2.trans ht.2⟩
      have hg := h.gap' hsI 1
      rw [abs_sub_comm] at hg
      have := abs_div_pow_le_of_le (c := 2) h.pos hg 2
      rwa [Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num] at *
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hb

theorem abs_I2_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) : |I2 W VL ω t| ≤ 2 / δ ^ 2 * t := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => 2 / ((v VL 0 ω s - w W ω s) * (v VL 1 ω s - w W ω s))) (C := 2 / δ ^ 2) fun s hs => by
      rw [uIoc_of_le ht.1] at hs
      have hsI : s ∈ Icc (0 : ℝ) S := ⟨hs.1.le, hs.2.trans ht.2⟩
      have hg0 := h.gap' hsI 0
      have hg1 := h.gap' hsI 1
      rw [abs_sub_comm] at hg0 hg1
      have := abs_div_mul_le_of_le (c := 2) h.pos hg0 hg1
      rwa [Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num] at *
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hb

end PathOn

end Path

/-! ### The drifted log-field -/

section Field

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin 2 → ℝ} {xR ρR : Fin 0 → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {S : Ω → ℝ≥0} {δ R : ℝ} {T : ℝ≥0}

/-- The field at the driver, at a fixed time, in terms of the processes. -/
theorem ell_driftDriver (r : ℝ≥0) (ω : Ω) :
    ell κ W VL ω r (driftDriver (Real.sqrt κ) B (D κ W B) ω r) =
      I1 W VL ω r - cy κ * Real.log (W r ω - VL 1 r ω) - cx κ * Real.log (W r ω - VL 0 r ω) +
        cxy κ * I2 W VL ω r := by
  simp only [ell, driftDriver_eq, w, v, Strip.extPath, Real.toNNReal_coe]

theorem ellX_driftDriver (r : ℝ≥0) (ω : Ω) :
    ellX κ VL ω r (driftDriver (Real.sqrt κ) B (D κ W B) ω r) =
      -cy κ / (W r ω - VL 1 r ω) - cx κ / (W r ω - VL 0 r ω) := by
  simp only [ellX, driftDriver_eq, w, v, Strip.extPath, Real.toNNReal_coe]

theorem ellXX_driftDriver (r : ℝ≥0) (ω : Ω) :
    ellXX κ VL ω r (driftDriver (Real.sqrt κ) B (D κ W B) ω r) =
      cy κ / (W r ω - VL 1 r ω) ^ 2 + cx κ / (W r ω - VL 0 r ω) ^ 2 := by
  simp only [ellXX, driftDriver_eq, w, v, Strip.extPath, Real.toNNReal_coe]

/-- `I1` and `I2` at a fixed time are measurable for the filtration at that time. -/
theorem measurable_I12 (hW : IsStronglyProgressive 𝓕 W) (hVL : ∀ i, IsStronglyProgressive 𝓕 (VL i)) (r : ℝ≥0) :
    Measurable[𝓕 r] (fun ω => I1 W VL ω r) ∧ Measurable[𝓕 r] (fun ω => I2 W VL ω r) := by
  have hp1 : IsStronglyProgressive 𝓕 fun t ω => 2 / (VL 1 t ω - W t ω) ^ 2 := fun i =>
    (measurable_const.div ((((hVL 1) i).measurable.sub (hW i).measurable).pow_const 2)).stronglyMeasurable
  have hp2 : IsStronglyProgressive 𝓕 fun t ω => 2 / ((VL 0 t ω - W t ω) * (VL 1 t ω - W t ω)) := fun i =>
    (measurable_const.div ((((hVL 0) i).measurable.sub (hW i).measurable).mul
      (((hVL 1) i).measurable.sub (hW i).measurable))).stronglyMeasurable
  exact ⟨A1Asm.measurable_integral_of_progressive hp1 r, A1Asm.measurable_integral_of_progressive hp2 r⟩

/-- **The inverse `SLE_κ(κ − 4, −4)` martingale's logarithm is a drifted log-field** over `[0, S]` along
`W = √κ B + D`, for a stopping time `S` before the lifetime and bounded by `T`, before which both force gaps lie in
`[δ, R]` at every sample. -/
theorem isDriftLogField_g3 (hκ : 0 < κ) (hp : ∀ ω, PathOn κ xL xR ρR W VL VR B ζ ω (S ω) δ)
    (hR : ∀ ω (r : ℝ≥0), r ≤ S ω → ∀ i, |W r ω - VL i r ω| ≤ R) (hST : ∀ ω, S ω ≤ T) (hδ : 0 < δ)
    (hW : IsStronglyProgressive 𝓕 W) (hVL : ∀ i, IsStronglyProgressive 𝓕 (VL i))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    ∃ K, IsDriftLogField 𝓕 (Real.sqrt κ) (δ / 8) K B (D κ W B) (drift κ W VL) 0 S (ell κ W VL) (ellX κ VL)
      (ellXX κ VL) (ellXXX κ VL) (ellT κ W VL) := by
  have hδ2 : 0 < δ / 2 := by positivity
  set c := |cy κ| + |cx κ| with hc
  set L := |Real.log (δ / 2)| + |Real.log (R + δ / 2)| with hL
  set Kℓ := 2 / δ ^ 2 * T * (1 + |cxy κ|) + c * L with hKℓ
  set Kx := c / (δ / 2) with hKx
  set Kxx := c / (δ / 2) ^ 2 with hKxx
  set Kxxx := 2 * c / (δ / 2) ^ 3 with hKxxx
  set Kt := 2 / δ ^ 2 + c * (2 / δ) / (δ / 2) + |cxy κ| * (2 / δ ^ 2) with hKt
  set Kb := (|κ - 4| + 4) / δ with hKb
  have hc0 : 0 ≤ c := by positivity
  have hL0 : 0 ≤ L := by positivity
  have nℓ : 0 ≤ Kℓ := by positivity
  have nx : 0 ≤ Kx := by positivity
  have nxx : 0 ≤ Kxx := by positivity
  have nxxx : 0 ≤ Kxxx := by positivity
  have nt : 0 ≤ Kt := by positivity
  have nb : 0 ≤ Kb := by positivity
  refine ⟨Kℓ + Kx + Kxx + Kxxx + Kt + Kb, ?_⟩
  have hfst : ∀ ω, ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 (S ω : ℝ)) → ContinuousOn (fun p : ℝ × ℝ => f p.1)
      (driftTube (Real.sqrt κ) B (D κ W B) ((0 : ℝ≥0) : ℝ) (S ω) (4 * (δ / 8)) ω) := fun ω f hf =>
    hf.comp continuousOn_fst fun p hp' => (mem_tube (hp ω) (hR ω) hp').1
  have hd : ∀ ω i, ContinuousOn (fun p : ℝ × ℝ => p.2 - v VL i ω p.1)
      (driftTube (Real.sqrt κ) B (D κ W B) ((0 : ℝ≥0) : ℝ) (S ω) (4 * (δ / 8)) ω) := fun ω i =>
    continuousOn_snd.sub (hfst ω _ ((hp ω).contV i))
  have hne := fun ω p (hp' : p ∈ driftTube (Real.sqrt κ) B (D κ W B) ((0 : ℝ≥0) : ℝ) (S ω) (4 * (δ / 8)) ω) i =>
    ne_of_mem_tube (hp ω) (hR ω) hp' i
  refine
    { le := fun _ => bot_le
      Knonneg := by positivity
      dD := fun ω t ht => ?_
      contb := fun ω => ?_
      bound_b := fun ω t ht => ?_
      dx := fun ω p hp' => hasDerivAt_ell ω p.1 p.2 (hne ω p hp' 0) (hne ω p hp' 1)
      dxx := fun ω p hp' => hasDerivAt_ellX ω p.1 p.2 (hne ω p hp' 0) (hne ω p hp' 1)
      dxxx := fun ω p hp' => hasDerivAt_ellXX ω p.1 p.2 (hne ω p hp' 0) (hne ω p hp' 1)
      dt := fun ω p hp' => ?_
      cont := fun ω => ?_
      contX := fun ω => ?_
      contXX := fun ω => ?_
      contT := fun ω => ?_
      bound := fun ω p hp' => ?_
      gen := fun ω t ht => ?_
      meas0 := fun r _ => ?_
      meas1 := fun r _ => ?_
      meas2 := fun r _ => ?_ }
  · rw [NNReal.coe_zero] at ht ⊢
    exact (hp ω).hasDerivWithinAt_D ht
  · rw [NNReal.coe_zero]
    exact (continuousOn_const.div ((hp ω).contW.sub ((hp ω).contV 0)) fun u hu => (hp ω).ne hu 0).add
      (continuousOn_const.div ((hp ω).contW.sub ((hp ω).contV 1)) fun u hu => (hp ω).ne hu 1)
  · rw [NNReal.coe_zero] at ht
    have b0 := abs_div_le_of_le (c := κ - 4) hδ ((hp ω).gap' ht 0)
    have b1 := abs_div_le_of_le (c := -4) hδ ((hp ω).gap' ht 1)
    have e4 : |(-4 : ℝ)| = 4 := by norm_num
    rw [e4] at b1
    have hb : |drift κ W VL ω t| ≤ Kb := by
      rw [hKb, add_div]
      exact (abs_add_le _ _).trans (add_le_add b0 b1)
    linarith
  · have hm := mem_tube (hp ω) (hR ω) hp'
    rw [NNReal.coe_zero]
    exact (hp ω).hasDerivWithinAt_ell hm.1 (hne ω p hp' 0) (hne ω p hp' 1)
  · exact (((hfst ω _ (hp ω).contI1).sub (continuousOn_const.mul ((hd ω 1).log fun p hp' => hne ω p hp' 1))).sub
      (continuousOn_const.mul ((hd ω 0).log fun p hp' => hne ω p hp' 0))).add
      (continuousOn_const.mul (hfst ω _ (hp ω).contI2))
  · exact (continuousOn_const.div (hd ω 1) fun p hp' => hne ω p hp' 1).sub
      (continuousOn_const.div (hd ω 0) fun p hp' => hne ω p hp' 0)
  · exact (continuousOn_const.div ((hd ω 1).pow 2) fun p hp' => pow_ne_zero 2 (hne ω p hp' 1)).add
      (continuousOn_const.div ((hd ω 0).pow 2) fun p hp' => pow_ne_zero 2 (hne ω p hp' 0))
  · have c1 : ContinuousOn (fun s => 2 / (v VL 1 ω s - w W ω s)) (Icc 0 (S ω : ℝ)) :=
      continuousOn_const.div (((hp ω).contV 1).sub (hp ω).contW) fun u hu => (hp ω).ne' hu 1
    have c0 : ContinuousOn (fun s => 2 / (v VL 0 ω s - w W ω s)) (Icc 0 (S ω : ℝ)) :=
      continuousOn_const.div (((hp ω).contV 0).sub (hp ω).contW) fun u hu => (hp ω).ne' hu 0
    exact (((hfst ω _ (hp ω).contI1').add ((continuousOn_const.mul (hfst ω _ c1)).div (hd ω 1)
      fun p hp' => hne ω p hp' 1)).add ((continuousOn_const.mul (hfst ω _ c0)).div (hd ω 0)
      fun p hp' => hne ω p hp' 0)).add (continuousOn_const.mul (hfst ω _ (hp ω).contI2'))
  · obtain ⟨ht, hb⟩ := mem_tube (hp ω) (hR ω) hp'
    have hT : (p.1 : ℝ) ≤ T := ht.2.trans (NNReal.coe_le_coe.2 (hST ω))
    have l1 := abs_log_le_of_le hδ2 (hb 1).1 (hb 1).2
    have l0 := abs_log_le_of_le hδ2 (hb 0).1 (hb 0).2
    have i1 : |I1 W VL ω p.1| ≤ 2 / δ ^ 2 * T :=
      ((hp ω).abs_I1_le ht).trans (mul_le_mul_of_nonneg_left hT (by positivity))
    have i2 : |I2 W VL ω p.1| ≤ 2 / δ ^ 2 * T :=
      ((hp ω).abs_I2_le ht).trans (mul_le_mul_of_nonneg_left hT (by positivity))
    have hcy : |cy κ| ≤ c := le_add_of_nonneg_right (abs_nonneg _)
    have hcx : |cx κ| ≤ c := le_add_of_nonneg_left (abs_nonneg _)
    -- `ℓ`
    have bℓ : |ell κ W VL ω p.1 p.2| ≤ Kℓ := by
      have e : ell κ W VL ω p.1 p.2 = I1 W VL ω p.1 - cy κ * Real.log (p.2 - v VL 1 ω p.1) -
          cx κ * Real.log (p.2 - v VL 0 ω p.1) + cxy κ * I2 W VL ω p.1 := rfl
      rw [e]
      calc _ ≤ |I1 W VL ω p.1| + |cy κ| * |Real.log (p.2 - v VL 1 ω p.1)| +
            |cx κ| * |Real.log (p.2 - v VL 0 ω p.1)| + |cxy κ| * |I2 W VL ω p.1| := by
            refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
              (add_le_add le_rfl (abs_mul _ _).le)) (abs_mul _ _).le)) (abs_mul _ _).le)
        _ ≤ 2 / δ ^ 2 * T + |cy κ| * L + |cx κ| * L + |cxy κ| * (2 / δ ^ 2 * T) := by
            gcongr
        _ = Kℓ := by rw [hKℓ, hc]; ring
    -- `ℓ_x`
    have bx : |ellX κ VL ω p.1 p.2| ≤ Kx := by
      have a1 := abs_div_le_of_le (c := -cy κ) hδ2 (hb 1).1
      have a0 := abs_div_le_of_le (c := cx κ) hδ2 (hb 0).1
      rw [abs_neg] at a1
      calc _ ≤ |cy κ| / (δ / 2) + |cx κ| / (δ / 2) := (abs_sub _ _).trans (add_le_add a1 a0)
        _ = Kx := by rw [hKx, hc, add_div]
    -- `ℓ_xx`
    have bxx : |ellXX κ VL ω p.1 p.2| ≤ Kxx := by
      have a1 := abs_div_pow_le_of_le (c := cy κ) hδ2 (hb 1).1 2
      have a0 := abs_div_pow_le_of_le (c := cx κ) hδ2 (hb 0).1 2
      calc _ ≤ |cy κ| / (δ / 2) ^ 2 + |cx κ| / (δ / 2) ^ 2 := (abs_add_le _ _).trans (add_le_add a1 a0)
        _ = Kxx := by rw [hKxx, hc, add_div]
    -- `ℓ_xxx`
    have bxxx : |ellXXX κ VL ω p.1 p.2| ≤ Kxxx := by
      have a1 := abs_div_pow_le_of_le (c := -(2 * cy κ)) hδ2 (hb 1).1 3
      have a0 := abs_div_pow_le_of_le (c := 2 * cx κ) hδ2 (hb 0).1 3
      rw [abs_neg, abs_mul] at a1
      rw [abs_mul] at a0
      calc _ ≤ |2| * |cy κ| / (δ / 2) ^ 3 + |2| * |cx κ| / (δ / 2) ^ 3 := (abs_sub _ _).trans (add_le_add a1 a0)
        _ = Kxxx := by rw [hKxxx, hc]; norm_num; ring
    -- `ℓ_t`
    have bt : |ellT κ W VL ω p.1 p.2| ≤ Kt := by
      have g1 := (hp ω).gap' ht 1
      have g0 := (hp ω).gap' ht 0
      rw [abs_sub_comm] at g1 g0
      have q1 : |2 / (v VL 1 ω p.1 - w W ω p.1) ^ 2| ≤ 2 / δ ^ 2 := by
        have := abs_div_pow_le_of_le (c := 2) hδ g1 2
        rwa [show |(2 : ℝ)| = 2 by norm_num] at this
      have r1 : |2 / (v VL 1 ω p.1 - w W ω p.1)| ≤ 2 / δ := by
        have := abs_div_le_of_le (c := 2) hδ g1
        rwa [show |(2 : ℝ)| = 2 by norm_num] at this
      have r0 : |2 / (v VL 0 ω p.1 - w W ω p.1)| ≤ 2 / δ := by
        have := abs_div_le_of_le (c := 2) hδ g0
        rwa [show |(2 : ℝ)| = 2 by norm_num] at this
      have q01 : |2 / ((v VL 0 ω p.1 - w W ω p.1) * (v VL 1 ω p.1 - w W ω p.1))| ≤ 2 / δ ^ 2 := by
        have := abs_div_mul_le_of_le (c := 2) hδ g0 g1
        rwa [show |(2 : ℝ)| = 2 by norm_num] at this
      have s1 : |cy κ * (2 / (v VL 1 ω p.1 - w W ω p.1)) / (p.2 - v VL 1 ω p.1)| ≤ |cy κ| * (2 / δ) / (δ / 2) := by
        refine (abs_div_le_of_le hδ2 (hb 1).1).trans ?_
        rw [abs_mul]
        gcongr
      have s0 : |cx κ * (2 / (v VL 0 ω p.1 - w W ω p.1)) / (p.2 - v VL 0 ω p.1)| ≤ |cx κ| * (2 / δ) / (δ / 2) := by
        refine (abs_div_le_of_le hδ2 (hb 0).1).trans ?_
        rw [abs_mul]
        gcongr
      have s2 : |cxy κ * (2 / ((v VL 0 ω p.1 - w W ω p.1) * (v VL 1 ω p.1 - w W ω p.1)))| ≤ |cxy κ| * (2 / δ ^ 2) := by
        rw [abs_mul]
        gcongr
      calc _ ≤ 2 / δ ^ 2 + |cy κ| * (2 / δ) / (δ / 2) + |cx κ| * (2 / δ) / (δ / 2) + |cxy κ| * (2 / δ ^ 2) :=
            (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
              (add_le_add q1 s1)) s0)) s2)
        _ = Kt := by rw [hKt, hc]; ring
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rw [NNReal.coe_zero] at ht
    rw [driftDriver_eq]
    exact gen_eq_zero hκ ω t ((hp ω).ne ht 0) ((hp ω).ne ht 1)
  · obtain ⟨h1, h2⟩ := measurable_I12 hW hVL r
    have hWr := (hW.stronglyAdapted r).measurable
    have h0r := ((hVL 0).stronglyAdapted r).measurable
    have h1r := ((hVL 1).stronglyAdapted r).measurable
    have e : (fun ω => ell κ W VL ω r (driftDriver (Real.sqrt κ) B (D κ W B) ω r)) = fun ω =>
        I1 W VL ω r - cy κ * Real.log (W r ω - VL 1 r ω) - cx κ * Real.log (W r ω - VL 0 r ω) +
          cxy κ * I2 W VL ω r := funext fun ω => ell_driftDriver r ω
    rw [e]
    exact (((h1.sub (measurable_const.mul (hWr.sub h1r).log)).sub (measurable_const.mul (hWr.sub h0r).log)).add
      (measurable_const.mul h2)).indicator (A1Common.measurableSet_le_stop hS r)
  · have hWr := (hW.stronglyAdapted r).measurable
    have h0r := ((hVL 0).stronglyAdapted r).measurable
    have h1r := ((hVL 1).stronglyAdapted r).measurable
    have e : (fun ω => ellX κ VL ω r (driftDriver (Real.sqrt κ) B (D κ W B) ω r)) = fun ω =>
        -cy κ / (W r ω - VL 1 r ω) - cx κ / (W r ω - VL 0 r ω) := funext fun ω => ellX_driftDriver r ω
    rw [e]
    exact ((measurable_const.div (hWr.sub h1r)).sub (measurable_const.div (hWr.sub h0r))).indicator
      (A1Common.measurableSet_le_stop hS r)
  · have hWr := (hW.stronglyAdapted r).measurable
    have h0r := ((hVL 0).stronglyAdapted r).measurable
    have h1r := ((hVL 1).stronglyAdapted r).measurable
    have e : (fun ω => ellXX κ VL ω r (driftDriver (Real.sqrt κ) B (D κ W B) ω r)) = fun ω =>
        cy κ / (W r ω - VL 1 r ω) ^ 2 + cx κ / (W r ω - VL 0 r ω) ^ 2 := funext fun ω => ellXX_driftDriver r ω
    rw [e]
    exact ((measurable_const.div ((hWr.sub h1r).pow_const 2)).add
      (measurable_const.div ((hWr.sub h0r).pow_const 2))).indicator (A1Common.measurableSet_le_stop hS r)

end Field

end G3Field

end InteractingSLE.ZhanGT4.A1G3Id
