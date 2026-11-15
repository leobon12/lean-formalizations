/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedPath

/-!
# Every two-seed solution is the clock construction of its logarithmic-clock angle

Packet PROVE-SEC2-JAC. The pathwise content of the uniqueness step in the proof of Theorem 2.2
(Specification p. 24, `source/spec/p001-048.md` L542–L546): take any path satisfying the
integrated equations of Definition 2.1 with one force point on each side, both started at `0`
(`0⁻, 0⁺`). Put `ℓ_t = V^R_t - V^L_t` (the separation) and `X_t = W_t - V^L_t`. Then

* `ℓ` is strictly increasing before the lifetime, with `ℓ_t = ∫_0^t (2/X + 2/(ℓ - X))`
  (`sepR_eq_integral`, `strictMonoOn_sepR`); in particular `ℓ_t > 0` for `t > 0`;
* with `u = log ℓ_t` ("the change of clock `u = log ℓ_t`") and the angle `U_u = X_{τ(u)} / e^u`,
  `τ(u)` the hitting time of level `e^u` by `ℓ` (`logAngle`), the path is recovered from `U` by
  the clocks of the two-seed construction (`TwoSeedClock.lean`):
  `t = t(u)`, `V^L_t = L^-(u)`, `V^R_t = L^+(u)`, `W_t = w(u)` at `u = log ℓ_t`
  (`clock_logAngle_eq`, …; "Integrating the force-point equations back from `-∞` recovers exactly
  `t, L^-, L^+`, and `w`").

So every two-seed solution is a deterministic function of its angle process; the law of the
solution is determined by the law of the angle process (whose identification with the stationary
Jacobi diffusion is the stochastic half of the step, not done here). The weights, `κ` and the
driving equation are not used: only the force-point equations, the ordering, integrability and the
null collision sets.

The change of variables uses no chain rule for absolutely continuous functions: the measure
`ℓ'(s) ds` on `(0, t_0]` is mapped by `ℓ` onto Lebesgue measure on `(0, ℓ_{t_0}]`
(`map_sepC_withDensity`, checked on half-lines), followed by the substitution `y = e^u`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

/-- The left gap `X_s = W_s - V^L_s` at real time `s` (read at `s.toNNReal`). -/
def gapLR (w : ℝ≥0 → ℝ) (vL : Fin 1 → ℝ≥0 → ℝ) (s : ℝ) : ℝ := w s.toNNReal - vL 0 s.toNNReal

/-- The right gap `Y_s = V^R_s - W_s` at real time `s`. -/
def gapRR (w : ℝ≥0 → ℝ) (vR : Fin 1 → ℝ≥0 → ℝ) (s : ℝ) : ℝ := vR 0 s.toNNReal - w s.toNNReal

/-- The separation rate `ℓ'_s = 2 / X_s + 2 / Y_s` (Lean's `x / 0 = 0` on the null collision sets). -/
def sepRate (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  2 / gapLR w vL s + 2 / gapRR w vR s

/-- The separation `ℓ_t = V^R_t - V^L_t`. -/
def sepN (vL vR : Fin 1 → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := vR 0 t - vL 0 t

section Facts

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

theorem path_vL_zero : vL 0 0 = 0 := by
  obtain ⟨-, h, -⟩ := h; exact h 0

theorem path_vR_zero : vR 0 0 = 0 := by
  obtain ⟨-, -, h, -⟩ := h; exact h 0

theorem path_continuousOn_w : ContinuousOn w {t | (t : ℝ≥0∞) < ζ} := by
  obtain ⟨-, -, -, h, -⟩ := h; exact h

theorem path_continuousOn_vL : ContinuousOn (vL 0) {t | (t : ℝ≥0∞) < ζ} := by
  obtain ⟨-, -, -, -, h, -⟩ := h; exact h 0

theorem path_continuousOn_vR : ContinuousOn (vR 0) {t | (t : ℝ≥0∞) < ζ} := by
  obtain ⟨-, -, -, -, -, h, -⟩ := h; exact h 0

theorem path_vL_le_w {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vL 0 t ≤ w t := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := h; exact h t ht 0

theorem path_w_le_vR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : w t ≤ vR 0 t := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := h; exact h t ht 0

theorem path_integrable_gapL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL 0 s.toNNReal)⁻¹) volume 0 t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h t ht 0

theorem path_integrable_gapR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR 0 s.toNNReal)⁻¹) volume 0 t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h t ht 0

theorem path_vL_eq {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    vL 0 t = 0 + ∫ s in (0 : ℝ)..t, 2 / (vL 0 s.toNNReal - w s.toNNReal) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h t ht 0

theorem path_vR_eq {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    vR 0 t = 0 + ∫ s in (0 : ℝ)..t, 2 / (vR 0 s.toNNReal - w s.toNNReal) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h t ht 0

theorem path_volume_collisionL :
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vL 0 s.toNNReal} = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h 0

theorem path_volume_collisionR :
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR 0 s.toNNReal} = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h 0

omit h in
/-- A real time in `[0, t]` with `t < ζ` is before `ζ`. -/
theorem toNNReal_lt_of_le {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ≤ t) :
    (s.toNNReal : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs) ht

theorem gapLR_nonneg {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ≤ t) : 0 ≤ gapLR w vL s :=
  sub_nonneg.2 (path_vL_le_w h (toNNReal_lt_of_le ht hs))

theorem gapRR_nonneg {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ≤ t) : 0 ≤ gapRR w vR s :=
  sub_nonneg.2 (path_w_le_vR h (toNNReal_lt_of_le ht hs))

theorem sepRate_nonneg {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ≤ t) :
    0 ≤ sepRate w vL vR s :=
  add_nonneg (div_nonneg zero_le_two (gapLR_nonneg h ht hs))
    (div_nonneg zero_le_two (gapRR_nonneg h ht hs))

theorem intervalIntegrable_two_div_gapLR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s => 2 / gapLR w vL s) volume 0 t := by
  simpa only [gapLR, div_eq_mul_inv] using (path_integrable_gapL h ht).const_mul 2

theorem intervalIntegrable_two_div_gapRR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s => 2 / gapRR w vR s) volume 0 t := by
  have := (path_integrable_gapR h ht).const_mul (-2)
  refine this.congr fun s _ => ?_
  simp only [gapRR]
  rw [← neg_sub, inv_neg, div_eq_mul_inv]
  ring

theorem intervalIntegrable_sepRate {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (sepRate w vL vR) volume 0 t :=
  (intervalIntegrable_two_div_gapLR h ht).add (intervalIntegrable_two_div_gapRR h ht)

/-- `V^L_t = -∫_0^t 2 / X_s ds`. -/
theorem vL_eq_neg_integral {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    vL 0 t = -∫ s in (0 : ℝ)..t, 2 / gapLR w vL s := by
  rw [path_vL_eq h ht, zero_add, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [gapLR]
  rw [← neg_sub, div_neg]

/-- `V^R_t = ∫_0^t 2 / Y_s ds`. -/
theorem vR_eq_integral {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    vR 0 t = ∫ s in (0 : ℝ)..t, 2 / gapRR w vR s := by
  rw [path_vR_eq h ht, zero_add]
  rfl

/-- `ℓ_t = ∫_0^t (2 / X_s + 2 / Y_s) ds`. -/
theorem sepN_eq_integral {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    sepN vL vR t = ∫ s in (0 : ℝ)..t, sepRate w vL vR s := by
  simp only [sepRate]
  rw [sepN, vL_eq_neg_integral h ht, vR_eq_integral h ht,
    intervalIntegral.integral_add (intervalIntegrable_two_div_gapLR h ht)
      (intervalIntegrable_two_div_gapRR h ht)]
  ring

/-- The separation, frozen after time `t₀`, as a function of real time (continuous on `ℝ`). -/
def sepC (vL vR : Fin 1 → ℝ≥0 → ℝ) (t₀ : ℝ≥0) (s : ℝ) : ℝ := sepN vL vR (min s t₀).toNNReal

omit h in
theorem sepC_of_le {t₀ : ℝ≥0} {s : ℝ} (hs : s ≤ t₀) : sepC vL vR t₀ s = sepN vL vR s.toNNReal := by
  rw [sepC, min_eq_left hs]

theorem continuous_sepC {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) : Continuous (sepC vL vR t₀) := by
  have hS : ContinuousOn (sepN vL vR) {t | (t : ℝ≥0∞) < ζ} :=
    (path_continuousOn_vR h).sub (path_continuousOn_vL h)
  refine hS.comp_continuous (continuous_real_toNNReal.comp (continuous_id.min continuous_const))
    fun s => ?_
  exact toNNReal_lt_of_le ht₀ (min_le_right _ _)

theorem sepC_zero (t₀ : ℝ≥0) : sepC vL vR t₀ 0 = 0 := by
  rw [sepC_of_le (NNReal.coe_nonneg t₀), Real.toNNReal_zero, sepN, path_vR_zero h, path_vL_zero h,
    sub_zero]

/-- `ℓ_s = ∫_0^s ℓ'` for `0 ≤ s ≤ t₀`. -/
theorem sepC_eq_integral {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ t₀) :
    sepC vL vR t₀ s = ∫ x in (0 : ℝ)..s, sepRate w vL vR x := by
  rw [sepC_of_le hs, sepN_eq_integral h (toNNReal_lt_of_le ht₀ hs), Real.coe_toNNReal _ hs0]

/-- **The separation is strictly increasing** before the lifetime: `ℓ_b - ℓ_a = ∫_a^b ℓ' > 0`,
since `ℓ' ≥ 2 / X > 0` off the null left collision set (Specification p. 24, L542: "Monotonicity and
the integral equations give `ℓ_t > 0` for `t > 0`"). -/
theorem strictMonoOn_sepC {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) :
    StrictMonoOn (sepC vL vR t₀) (Icc 0 t₀) := by
  intro a ha c hc hac
  have hint := intervalIntegrable_sepRate h ht₀
  have hsub : sepC vL vR t₀ c - sepC vL vR t₀ a = ∫ x in a..c, sepRate w vL vR x := by
    rw [sepC_eq_integral h ht₀ ha.1 ha.2, sepC_eq_integral h ht₀ hc.1 hc.2,
      intervalIntegral.integral_interval_sub_left (hint.mono_set ?_) (hint.mono_set ?_)]
    · rw [uIcc_of_le hc.1, uIcc_of_le (NNReal.coe_nonneg t₀)]; exact Icc_subset_Icc le_rfl hc.2
    · rw [uIcc_of_le ha.1, uIcc_of_le (NNReal.coe_nonneg t₀)]; exact Icc_subset_Icc le_rfl ha.2
  have hpos : 0 < ∫ x in a..c, sepRate w vL vR x := by
    have hint' : IntervalIntegrable (sepRate w vL vR) volume a c := by
      refine hint.mono_set ?_
      rw [uIcc_of_le hac.le, uIcc_of_le (NNReal.coe_nonneg t₀)]
      exact Icc_subset_Icc ha.1 hc.2
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' ?_ hint']
    · refine ⟨hac, ?_⟩
      set C := {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vL 0 s.toNNReal}
      have hsub' : Ioc a c \ C ⊆ Function.support (sepRate w vL vR) ∩ Ioc a c := by
        rintro s ⟨hs, hsC⟩
        refine ⟨?_, hs⟩
        have hs0 : 0 ≤ s := ha.1.trans hs.1.le
        have hst : s ≤ t₀ := hs.2.trans hc.2
        have hne : w s.toNNReal ≠ vL 0 s.toNNReal := fun he =>
          hsC ⟨hs0, toNNReal_lt_of_le ht₀ hst, he⟩
        have hX : 0 < gapLR w vL s :=
          lt_of_le_of_ne (gapLR_nonneg h ht₀ hst) (Ne.symm (sub_ne_zero.2 hne))
        have := div_nonneg zero_le_two (gapRR_nonneg h ht₀ hst)
        have : 0 < 2 / gapLR w vL s := div_pos zero_lt_two hX
        exact (show 0 < sepRate w vL vR s by unfold sepRate; linarith).ne'
      calc (0 : ℝ≥0∞) < volume (Ioc a c \ C) := by
            rw [measure_sdiff_null (path_volume_collisionL h), Real.volume_Ioc]
            exact ENNReal.ofReal_pos.2 (sub_pos.2 hac)
        _ ≤ _ := measure_mono hsub'
    · rw [uIoc_of_le hac.le]
      refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_)
      exact sepRate_nonneg h ht₀ (hs.2.trans hc.2)
  linarith

theorem sepN_lt_sepN {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {s₁ s₂ : ℝ≥0} (h12 : s₁ < s₂)
    (h2 : s₂ ≤ t₀) : sepN vL vR s₁ < sepN vL vR s₂ := by
  have h1' : (s₁ : ℝ) ≤ t₀ := by exact_mod_cast h12.le.trans h2
  have h2' : (s₂ : ℝ) ≤ t₀ := by exact_mod_cast h2
  have := strictMonoOn_sepC h ht₀ ⟨NNReal.coe_nonneg s₁, h1'⟩ ⟨NNReal.coe_nonneg s₂, h2'⟩
    (show (s₁ : ℝ) < s₂ by exact_mod_cast h12)
  rwa [sepC_of_le h1', sepC_of_le h2', Real.toNNReal_coe, Real.toNNReal_coe] at this

theorem sepN_zero : sepN vL vR 0 = 0 := by
  rw [sepN, path_vR_zero h, path_vL_zero h, sub_zero]

/-- `ℓ_t > 0` for `0 < t < ζ`. -/
theorem sepN_pos {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (ht0 : 0 < t) : 0 < sepN vL vR t := by
  have := sepN_lt_sepN h ht ht0 le_rfl
  rwa [sepN_zero h] at this

theorem le_sepN_of_le {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {s₁ s₂ : ℝ≥0} (h12 : s₁ ≤ s₂)
    (h2 : s₂ ≤ t₀) : sepN vL vR s₁ ≤ sepN vL vR s₂ := by
  rcases h12.eq_or_lt with rfl | h12
  · exact le_rfl
  · exact (sepN_lt_sepN h ht₀ h12 h2).le

theorem sepN_le_sepN_iff {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {s₁ s₂ : ℝ≥0} (h1 : s₁ ≤ t₀)
    (h2 : s₂ ≤ t₀) : sepN vL vR s₁ ≤ sepN vL vR s₂ ↔ s₁ ≤ s₂ := by
  refine ⟨fun hle => not_lt.1 fun hlt => ?_, fun hle => le_sepN_of_le h ht₀ hle h2⟩
  exact absurd hle (not_le.2 (sepN_lt_sepN h ht₀ hlt h1))

end Facts

/-- The hitting time `τ(u)` of the level `e^u` by the separation `ℓ` before the lifetime. -/
def hitTime (vL vR : Fin 1 → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (u : ℝ) : ℝ≥0 :=
  sInf {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ exp u ≤ sepN vL vR s}

/-- The angle process in the logarithmic clock, `U_u = X_{τ(u)} / e^u = (W - V^L)/(V^R - V^L)` at
the time `τ(u)` when the separation is `e^u`. -/
def logAngle (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (u : ℝ) : ℝ :=
  (w (hitTime vL vR ζ u) - vL 0 (hitTime vL vR ζ u)) / exp u

section HitTime

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

theorem isLeast_hitTime {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {u : ℝ} {s : ℝ≥0} (hs : s ≤ t₀)
    (hsu : sepN vL vR s = exp u) :
    IsLeast {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ exp u ≤ sepN vL vR s} s := by
  refine ⟨⟨lt_of_le_of_lt (by exact_mod_cast hs) ht₀, hsu.ge⟩, fun s' ⟨_, hs'⟩ => ?_⟩
  rcases le_or_gt s' t₀ with h' | h'
  · exact (sepN_le_sepN_iff h ht₀ hs h').1 (hsu.le.trans hs')
  · exact hs.trans h'.le

/-- For `e^u ≤ ℓ_{t₀}`, the hitting time is at most `t₀` and `ℓ_{τ(u)} = e^u`. -/
theorem hitTime_spec {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {u : ℝ} (hu : exp u ≤ sepN vL vR t₀) :
    hitTime vL vR ζ u ≤ t₀ ∧ sepN vL vR (hitTime vL vR ζ u) = exp u := by
  have hc := continuous_sepC h ht₀
  have h0 : sepC vL vR t₀ 0 ≤ exp u := by rw [sepC_zero h]; exact (exp_pos u).le
  have h1 : exp u ≤ sepC vL vR t₀ t₀ := by
    rwa [sepC_of_le le_rfl, Real.toNNReal_coe]
  obtain ⟨c, hc', hcu⟩ := intermediate_value_Icc (NNReal.coe_nonneg t₀) hc.continuousOn ⟨h0, h1⟩
  have hct : c.toNNReal ≤ t₀ := Real.toNNReal_le_iff_le_coe.2 hc'.2
  have hsu : sepN vL vR c.toNNReal = exp u := by rw [← sepC_of_le hc'.2, hcu]
  have := (isLeast_hitTime h ht₀ hct hsu).csInf_eq
  rw [hitTime, this]
  exact ⟨hct, hsu⟩

/-- `τ(log ℓ_s) = s` for `0 < s < ζ`. -/
theorem hitTime_log_sepN {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) (hs0 : 0 < s) :
    hitTime vL vR ζ (log (sepN vL vR s)) = s := by
  have hpos := sepN_pos h hs hs0
  rw [hitTime, (isLeast_hitTime h hs le_rfl (exp_log hpos).symm).csInf_eq]

theorem monotoneOn_hitTime {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) :
    MonotoneOn (hitTime vL vR ζ) {u | exp u ≤ sepN vL vR t₀} := by
  intro u₁ hu₁ u₂ hu₂ h12
  obtain ⟨h1, e1⟩ := hitTime_spec h ht₀ hu₁
  obtain ⟨h2, e2⟩ := hitTime_spec h ht₀ hu₂
  refine (sepN_le_sepN_iff h ht₀ h1 h2).1 ?_
  rw [e1, e2]
  exact exp_le_exp.2 h12

theorem logAngle_mem_Icc {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {u : ℝ} (hu : exp u ≤ sepN vL vR t₀) :
    logAngle w vL vR ζ u ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, e1⟩ := hitTime_spec h ht₀ hu
  have hlt : ((hitTime vL vR ζ u : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast h1) ht₀
  have hX := path_vL_le_w h hlt
  have hY := path_w_le_vR h hlt
  rw [sepN] at e1
  rw [logAngle, ← e1]
  have hpos : 0 < vR 0 (hitTime vL vR ζ u) - vL 0 (hitTime vL vR ζ u) := by rw [e1]; exact exp_pos u
  refine ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).2 (by linarith)⟩

/-- At `u = log ℓ_s`, the angle is `X_s / ℓ_s`. -/
theorem logAngle_log_sepN {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) (hs0 : 0 < s) :
    logAngle w vL vR ζ (log (sepN vL vR s)) = (w s - vL 0 s) / sepN vL vR s := by
  rw [logAngle, hitTime_log_sepN h hs hs0, exp_log (sepN_pos h hs hs0)]

end HitTime

/-- `exp` maps `(-∞, a]` onto `(0, e^a]`. -/
theorem exp_image_Iic (a : ℝ) : exp '' Iic a = Ioc 0 (exp a) := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨exp_pos v, exp_le_exp.2 hv⟩
  · rintro ⟨hy0, hya⟩
    exact ⟨log y, (log_le_iff_le_exp hy0).2 hya, exp_log hy0⟩

/-- The substitution `y = e^v`: `∫⁻_{(0, e^a]} G = ∫⁻_{(-∞, a]} e^v G(e^v) dv`. -/
theorem lintegral_Ioc_exp (a : ℝ) (G : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ioc 0 (exp a), G y = ∫⁻ v in Iic a, ENNReal.ofReal (exp v) * G (exp v) := by
  rw [← exp_image_Iic, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Iic
    (fun v _ => (hasDerivAt_exp v).hasDerivWithinAt) exp_injective.injOn G]
  refine setLIntegral_congr_fun measurableSet_Iic fun v _ => ?_
  rw [abs_of_pos (exp_pos v)]

section Pushforward

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

theorem sepC_nonneg {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t₀) :
    0 ≤ sepC vL vR t₀ s := by
  rw [← sepC_zero h t₀]
  exact (strictMonoOn_sepC h ht₀).monotoneOn ⟨le_rfl, NNReal.coe_nonneg t₀⟩ hs hs.1

theorem sepC_le {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t₀) :
    sepC vL vR t₀ s ≤ sepN vL vR t₀ := by
  have := (strictMonoOn_sepC h ht₀).monotoneOn hs ⟨NNReal.coe_nonneg t₀, le_rfl⟩ hs.2
  rwa [sepC_of_le le_rfl, Real.toNNReal_coe] at this

/-- **The separation maps `ℓ'(s) ds` on `(0, t₀]` onto Lebesgue measure on `(0, ℓ_{t₀}]`.** -/
theorem map_sepC_withDensity {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) :
    ((volume.restrict (Ioc (0 : ℝ) t₀)).withDensity
        (fun s => ENNReal.ofReal (sepRate w vL vR s))).map (sepC vL vR t₀) =
      volume.restrict (Ioc 0 (sepN vL vR t₀)) := by
  have hint : IntegrableOn (sepRate w vL vR) (Ioc 0 t₀) := (intervalIntegrable_sepRate h ht₀).1
  have hc := continuous_sepC h ht₀
  have : IsFiniteMeasure ((volume.restrict (Ioc (0 : ℝ) t₀)).withDensity
      (fun s => ENNReal.ofReal (sepRate w vL vR s))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hint.lintegral_lt_top
  refine Measure.ext_of_Iic _ _ fun c => ?_
  rw [Measure.map_apply hc.measurable measurableSet_Iic,
    withDensity_apply _ (hc.measurable measurableSet_Iic), Measure.restrict_restrict
      (hc.measurable measurableSet_Iic), Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge c 0 with hc0 | hc0
  · have h1 : sepC vL vR t₀ ⁻¹' Iic c ∩ Ioc 0 t₀ = ∅ := by
      ext s
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false,
        not_and]
      intro hsc hs0 hst
      linarith [sepC_nonneg h ht₀ ⟨hs0.le, hst⟩]
    have h2 : Iic c ∩ Ioc 0 (sepN vL vR t₀) = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro hyc hy0
      linarith
    rw [h1, h2, Measure.restrict_empty, lintegral_zero_measure, measure_empty]
  · set c' := min c (sepN vL vR t₀) with hc'
    have hc'0 : 0 ≤ c' := le_min hc0 (by
      have := sepC_le h ht₀ ⟨le_rfl, NNReal.coe_nonneg t₀⟩; linarith [sepC_zero h t₀ (vL := vL)])
    have hcle : c' ≤ sepC vL vR t₀ t₀ := by
      rw [sepC_of_le le_rfl, Real.toNNReal_coe]; exact min_le_right _ _
    obtain ⟨σ, hσ, hσc⟩ := intermediate_value_Icc (NNReal.coe_nonneg t₀) hc.continuousOn
      ⟨(sepC_zero h t₀).le.trans hc'0, hcle⟩
    have h1 : sepC vL vR t₀ ⁻¹' Iic c ∩ Ioc 0 t₀ = Ioc 0 σ := by
      ext s
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨hsc, hs0, hst⟩
        refine ⟨hs0, ((strictMonoOn_sepC h ht₀).le_iff_le ⟨hs0.le, hst⟩ hσ).1 ?_⟩
        rw [hσc]
        exact le_min hsc (sepC_le h ht₀ ⟨hs0.le, hst⟩)
      · rintro ⟨hs0, hsσ⟩
        have hst : s ≤ t₀ := hsσ.trans hσ.2
        refine ⟨?_, hs0, hst⟩
        have := ((strictMonoOn_sepC h ht₀).le_iff_le ⟨hs0.le, hst⟩ hσ).2 hsσ
        rw [hσc] at this
        exact this.trans (min_le_left _ _)
    have h2 : Iic c ∩ Ioc 0 (sepN vL vR t₀) = Ioc 0 c' := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, hc', le_min_iff]
      tauto
    rw [h1, h2, Real.volume_Ioc, sub_zero, ← ofReal_integral_eq_lintegral_ofReal
      (hint.mono_set (Ioc_subset_Ioc le_rfl hσ.2))
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs =>
        sepRate_nonneg h ht₀ (hs.2.trans hσ.2))), ← intervalIntegral.integral_of_le hσ.1,
      ← sepC_eq_integral h ht₀ hσ.1 hσ.2, hσc]

/-- **Change of variables along the separation**: for `G` a.e.-measurable on `(0, ℓ_{t₀}]`,
`∫⁻_{(0, t₀]} G(ℓ_s) ℓ'(s) ds = ∫⁻_{(0, ℓ_{t₀}]} G(y) dy`. -/
theorem lintegral_comp_sepC {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (G : ℝ → ℝ≥0∞)
    (hG : AEMeasurable G (volume.restrict (Ioc 0 (sepN vL vR t₀)))) :
    ∫⁻ s in Ioc 0 (t₀ : ℝ), ENNReal.ofReal (sepRate w vL vR s) * G (sepC vL vR t₀ s) =
      ∫⁻ y in Ioc 0 (sepN vL vR t₀), G y := by
  have hc := continuous_sepC h ht₀
  have hf : AEMeasurable (fun s => ENNReal.ofReal (sepRate w vL vR s))
      (volume.restrict (Ioc (0 : ℝ) t₀)) :=
    (intervalIntegrable_sepRate h ht₀).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [← map_sepC_withDensity h ht₀] at hG ⊢
  rw [lintegral_map' hG hc.aemeasurable]
  exact (lintegral_withDensity_eq_lintegral_mul₀' hf (hG.comp_aemeasurable hc.aemeasurable)).symm

end Pushforward

/-- The left gap, frozen after time `t₀` (continuous on `ℝ≥0`). -/
def gapC (w : ℝ≥0 → ℝ) (vL : Fin 1 → ℝ≥0 → ℝ) (t₀ : ℝ≥0) (s : ℝ≥0) : ℝ :=
  w (min s t₀) - vL 0 (min s t₀)

section Recovery

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

theorem continuous_gapC {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) : Continuous (gapC w vL t₀) := by
  have : ContinuousOn (fun s => w s - vL 0 s) {t | (t : ℝ≥0∞) < ζ} :=
    (path_continuousOn_w h).sub (path_continuousOn_vL h)
  exact this.comp_continuous (continuous_id.min continuous_const) fun s =>
    lt_of_le_of_lt (by exact_mod_cast min_le_right s t₀) ht₀

theorem logAngle_eq_gapC {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {u : ℝ}
    (hu : exp u ≤ sepN vL vR t₀) :
    logAngle w vL vR ζ u = gapC w vL t₀ (hitTime vL vR ζ u) / exp u := by
  rw [logAngle, gapC, min_eq_left (hitTime_spec h ht₀ hu).1]

/-- The angle process is a.e.-measurable on `(-∞, log ℓ_{t₀}]`. -/
theorem aemeasurable_logAngle {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (hpos : 0 < sepN vL vR t₀) :
    AEMeasurable (logAngle w vL vR ζ) (volume.restrict (Iic (log (sepN vL vR t₀)))) := by
  have hset : Iic (log (sepN vL vR t₀)) = {u | exp u ≤ sepN vL vR t₀} := by
    ext u; exact le_log_iff_exp_le hpos
  have hτ : AEMeasurable (fun u => hitTime vL vR ζ u)
      (volume.restrict (Iic (log (sepN vL vR t₀)))) := by
    rw [hset]
    exact aemeasurable_restrict_of_monotoneOn (measurableSet_le measurable_exp measurable_const)
      (monotoneOn_hitTime h ht₀)
  have : AEMeasurable (fun u => gapC w vL t₀ (hitTime vL vR ζ u) / exp u)
      (volume.restrict (Iic (log (sepN vL vR t₀)))) :=
    ((continuous_gapC h ht₀).measurable.comp_aemeasurable hτ).div measurable_exp.aemeasurable
  refine this.congr ((ae_restrict_iff' measurableSet_Iic).2 (ae_of_all _ fun u hu => ?_))
  exact (logAngle_eq_gapC h ht₀ ((le_log_iff_exp_le hpos).1 hu)).symm

/-- The angle process read at level `y`, `y ↦ U(log y)`, is a.e.-measurable on `(0, ℓ_{t₀}]`. -/
theorem aemeasurable_logAngle_log {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) :
    AEMeasurable (fun y => logAngle w vL vR ζ (log y)) (volume.restrict (Ioc 0 (sepN vL vR t₀))) := by
  have hmono : MonotoneOn (fun y => hitTime vL vR ζ (log y)) (Ioc 0 (sepN vL vR t₀)) := by
    intro y₁ hy₁ y₂ hy₂ h12
    refine monotoneOn_hitTime h ht₀ ?_ ?_ (log_le_log hy₁.1 h12)
    · simp only [mem_ofPred_eq, exp_log hy₁.1]; exact hy₁.2
    · simp only [mem_ofPred_eq, exp_log hy₂.1]; exact hy₂.2
  have hτ := aemeasurable_restrict_of_monotoneOn (μ := volume) measurableSet_Ioc hmono
  have : AEMeasurable (fun y => gapC w vL t₀ (hitTime vL vR ζ (log y)) / y)
      (volume.restrict (Ioc 0 (sepN vL vR t₀))) :=
    ((continuous_gapC h ht₀).measurable.comp_aemeasurable hτ).div aemeasurable_id
  refine this.congr ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun y hy => ?_))
  have hy' : exp (log y) ≤ sepN vL vR t₀ := by rw [exp_log hy.1]; exact hy.2
  simp only
  rw [logAngle_eq_gapC h ht₀ hy', exp_log hy.1]

omit h in
/-- `ℓ_s = X_s + Y_s`. -/
theorem sepC_eq_add {t₀ : ℝ≥0} {s : ℝ} (hs : s ≤ t₀) :
    sepC vL vR t₀ s = gapLR w vL s + gapRR w vR s := by
  rw [sepC_of_le hs, sepN, gapLR, gapRR]; ring

/-- Off the null collision sets, both gaps are positive. -/
theorem ae_gaps_pos {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) :
    ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) t₀ → 0 < gapLR w vL s ∧ 0 < gapRR w vR s := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (path_volume_collisionL h),
    measure_eq_zero_iff_ae_notMem.1 (path_volume_collisionR h)] with s hL hR hs
  have hζ := toNNReal_lt_of_le ht₀ hs.2
  refine ⟨lt_of_le_of_ne (gapLR_nonneg h ht₀ hs.2) fun he => hL ⟨hs.1.le, hζ, ?_⟩,
    lt_of_le_of_ne (gapRR_nonneg h ht₀ hs.2) fun he => hR ⟨hs.1.le, hζ, ?_⟩⟩
  · exact (sub_eq_zero.1 he.symm)
  · exact (sub_eq_zero.1 he.symm).symm

/-- At a real time `s ∈ (0, t₀]`, the angle at level `ℓ_s` is `X_s / ℓ_s`. -/
theorem logAngle_log_sepC {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) t₀) :
    logAngle w vL vR ζ (log (sepC vL vR t₀ s)) = gapLR w vL s / sepC vL vR t₀ s := by
  rw [sepC_of_le hs.2, logAngle_log_sepN h (toNNReal_lt_of_le ht₀ hs.2)
    (Real.toNNReal_pos.2 hs.1)]
  rfl

/-- **The generic recovery identity, lintegral form.** For `F` measurable and `g` with
`ℓ'_s F(ℓ_s, X_s/ℓ_s) = g_s` a.e. on `(0, t₀]`:
`∫⁻_{-∞}^{log ℓ_{t₀}} (e^v F(e^v, U_v))⁺ dv = ∫⁻_0^{t₀} g⁺`. -/
theorem lintegral_exp_mul_logAngle_eq {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀)
    (F : ℝ → ℝ → ℝ) (hFm : Measurable (Function.uncurry F)) (g : ℝ → ℝ)
    (hg : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) t₀ →
      sepRate w vL vR s * F (sepC vL vR t₀ s) (gapLR w vL s / sepC vL vR t₀ s) = g s) :
    ∫⁻ v in Iic (log (sepN vL vR t₀)), ENNReal.ofReal (exp v * F (exp v) (logAngle w vL vR ζ v)) =
      ∫⁻ s in Ioc 0 (t₀ : ℝ), ENNReal.ofReal (g s) := by
  have hpos := sepN_pos h ht₀ ht0
  set v₀ := log (sepN vL vR t₀)
  set G : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (F y (logAngle w vL vR ζ (log y)))
  have hGm : AEMeasurable G (volume.restrict (Ioc 0 (sepN vL vR t₀))) :=
    (hFm.comp_aemeasurable (aemeasurable_id.prodMk
      (aemeasurable_logAngle_log h ht₀))).ennreal_ofReal
  calc ∫⁻ v in Iic v₀, ENNReal.ofReal (exp v * F (exp v) (logAngle w vL vR ζ v))
      = ∫⁻ v in Iic v₀, ENNReal.ofReal (exp v) * G (exp v) := by
        refine setLIntegral_congr_fun measurableSet_Iic fun v _ => ?_
        simp only [G, log_exp, ENNReal.ofReal_mul (exp_pos v).le]
    _ = ∫⁻ y in Ioc 0 (sepN vL vR t₀), G y := by
        rw [← lintegral_Ioc_exp, exp_log hpos]
    _ = ∫⁻ s in Ioc 0 (t₀ : ℝ), ENNReal.ofReal (sepRate w vL vR s) * G (sepC vL vR t₀ s) :=
        (lintegral_comp_sepC h ht₀ G hGm).symm
    _ = ∫⁻ s in Ioc 0 (t₀ : ℝ), ENNReal.ofReal (g s) := by
        refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
        filter_upwards [hg] with s hs hsI
        simp only [G]
        rw [logAngle_log_sepC h ht₀ hsI, ← ENNReal.ofReal_mul (sepRate_nonneg h ht₀ hsI.2),
          hs hsI]

/-- **The generic recovery identity.** For `F` measurable, `≥ 0` on `(0, ∞) × [0, 1]`, and `g ≥ 0`
with `ℓ'_s F(ℓ_s, X_s/ℓ_s) = g_s` a.e. on `(0, t₀]`:
`∫_{-∞}^{log ℓ_{t₀}} e^v F(e^v, U_v) dv = ∫_0^{t₀} g`. -/
theorem integral_exp_mul_logAngle_eq {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀)
    (F : ℝ → ℝ → ℝ) (hFm : Measurable (Function.uncurry F))
    (hF0 : ∀ y a, 0 < y → a ∈ Icc (0 : ℝ) 1 → 0 ≤ F y a) (g : ℝ → ℝ)
    (hg0 : ∀ s ∈ Ioc (0 : ℝ) t₀, 0 ≤ g s)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioc 0 t₀)))
    (hg : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) t₀ →
      sepRate w vL vR s * F (sepC vL vR t₀ s) (gapLR w vL s / sepC vL vR t₀ s) = g s) :
    ∫ v in Iic (log (sepN vL vR t₀)), exp v * F (exp v) (logAngle w vL vR ζ v) =
      ∫ s in Ioc 0 (t₀ : ℝ), g s := by
  have hpos := sepN_pos h ht₀ ht0
  set v₀ := log (sepN vL vR t₀)
  have hU := aemeasurable_logAngle h ht₀ hpos
  have hLm : AEStronglyMeasurable (fun v => exp v * F (exp v) (logAngle w vL vR ζ v))
      (volume.restrict (Iic v₀)) :=
    (measurable_exp.aemeasurable.mul (hFm.comp_aemeasurable
      (measurable_exp.aemeasurable.prodMk hU))).aestronglyMeasurable
  have hL0 : 0 ≤ᵐ[volume.restrict (Iic v₀)] fun v => exp v * F (exp v) (logAngle w vL vR ζ v) := by
    refine (ae_restrict_iff' measurableSet_Iic).2 (ae_of_all _ fun v hv => ?_)
    have hv' : exp v ≤ sepN vL vR t₀ := (le_log_iff_exp_le hpos).1 hv
    exact mul_nonneg (exp_pos v).le (hF0 _ _ (exp_pos v) (logAngle_mem_Icc h ht₀ hv'))
  have hg0' : 0 ≤ᵐ[volume.restrict (Ioc 0 (t₀ : ℝ))] g :=
    (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hg0)
  rw [integral_eq_lintegral_of_nonneg_ae hL0 hLm, integral_eq_lintegral_of_nonneg_ae hg0' hgm,
    lintegral_exp_mul_logAngle_eq h ht₀ ht0 F hFm g hg]

/-- **The physical clock is recovered**: `t = t(log ℓ_t) = ½ ∫_{-∞}^{log ℓ_t} e^{2v} U_v (1 - U_v) dv`
for `0 < t < ζ`. -/
theorem clock_logAngle_eq {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀) :
    clock (logAngle w vL vR ζ) (log (sepN vL vR t₀)) = t₀ := by
  have key := integral_exp_mul_logAngle_eq h ht₀ ht0 (fun y a => y * (a * (1 - a)) / 2)
    (by fun_prop : Continuous _).measurable
    (fun y a hy ha => div_nonneg (mul_nonneg hy.le (mul_one_sub_mem_Icc ha).1) zero_le_two)
    (fun _ => 1) (fun _ _ => zero_le_one) aestronglyMeasurable_const ?_
  · rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal (NNReal.coe_nonneg t₀)] at key
    rw [← key, clock]
    refine setIntegral_congr_fun measurableSet_Iic fun v _ => ?_
    simp only [clockDensity]
    rw [show exp (2 * v) = exp v * exp v by rw [← exp_add]; ring_nf]
    ring
  · filter_upwards [ae_gaps_pos h ht₀] with s hs hsI
    obtain ⟨hX, hY⟩ := hs hsI
    rw [sepC_eq_add hsI.2, sepRate]
    field_simp
    ring

/-- **The left force point is recovered**: `V^L_t = L^-(log ℓ_t)` for `0 < t < ζ`. -/
theorem vL_eq_lowerL_logAngle {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀) :
    vL 0 t₀ = lowerL (logAngle w vL vR ζ) (log (sepN vL vR t₀)) := by
  have key := integral_exp_mul_logAngle_eq h ht₀ ht0 (fun _ a => 1 - a)
    (by fun_prop : Continuous _).measurable
    (fun _ a _ ha => sub_nonneg.2 ha.2) (fun s => 2 / gapLR w vL s)
    (fun s hs => div_nonneg zero_le_two (gapLR_nonneg h ht₀ hs.2))
    (intervalIntegrable_two_div_gapLR h ht₀).1.aestronglyMeasurable ?_
  · rw [lowerL, key, vL_eq_neg_integral h ht₀, intervalIntegral.integral_of_le (NNReal.coe_nonneg t₀)]
  · filter_upwards [ae_gaps_pos h ht₀] with s hs hsI
    obtain ⟨hX, hY⟩ := hs hsI
    rw [sepC_eq_add hsI.2, sepRate]
    field_simp
    ring

/-- **The right force point is recovered**: `V^R_t = L^+(log ℓ_t)` for `0 < t < ζ`. -/
theorem vR_eq_upperL_logAngle {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀) :
    vR 0 t₀ = upperL (logAngle w vL vR ζ) (log (sepN vL vR t₀)) := by
  have key := integral_exp_mul_logAngle_eq h ht₀ ht0 (fun _ a => a)
    (by fun_prop : Continuous _).measurable
    (fun _ a _ ha => ha.1) (fun s => 2 / gapRR w vR s)
    (fun s hs => div_nonneg zero_le_two (gapRR_nonneg h ht₀ hs.2))
    (intervalIntegrable_two_div_gapRR h ht₀).1.aestronglyMeasurable ?_
  · rw [upperL, key, vR_eq_integral h ht₀, intervalIntegral.integral_of_le (NNReal.coe_nonneg t₀)]
  · filter_upwards [ae_gaps_pos h ht₀] with s hs hsI
    obtain ⟨hX, hY⟩ := hs hsI
    rw [sepC_eq_add hsI.2, sepRate]
    field_simp
    ring

/-- **The driving point is recovered**: `W_t = w(log ℓ_t)` for `0 < t < ζ`. -/
theorem w_eq_driver_logAngle {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀) :
    w t₀ = driver (logAngle w vL vR ζ) (log (sepN vL vR t₀)) := by
  have hpos := sepN_pos h ht₀ ht0
  rw [driver, ← vL_eq_lowerL_logAngle h ht₀ ht0, logAngle_log_sepN h ht₀ ht0, exp_log hpos,
    mul_div_cancel₀ _ hpos.ne']
  ring

/-- **Every two-seed solution is the clock construction of its angle process** (Specification
p. 24, L546): for `0 < t < ζ`, with `u = log ℓ_t` and `U` the angle in the logarithmic clock,
`t = t(u)`, `V^L_t = L^-(u)`, `V^R_t = L^+(u)` and `W_t = w(u)`. -/
theorem eq_twoSeed_logAngle {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (ht0 : 0 < t) :
    clock (logAngle w vL vR ζ) (log (sepN vL vR t)) = t ∧
      vL 0 t = lowerL (logAngle w vL vR ζ) (log (sepN vL vR t)) ∧
      vR 0 t = upperL (logAngle w vL vR ζ) (log (sepN vL vR t)) ∧
      w t = driver (logAngle w vL vR ζ) (log (sepN vL vR t)) :=
  ⟨clock_logAngle_eq h ht ht0, vL_eq_lowerL_logAngle h ht ht0, vR_eq_upperL_logAngle h ht ht0,
    w_eq_driver_logAngle h ht ht0⟩

/-- `8 t ≤ ℓ_t²` before the lifetime (the source has `16 t ≤ ℓ_t²`, from `d(ℓ²)/dt ≥ 16`); in
particular `ℓ_t → ∞` if the lifetime is infinite. -/
theorem eight_mul_le_sepN_sq {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : 8 * (t : ℝ) ≤ sepN vL vR t ^ 2 := by
  rcases eq_zero_or_pos t with rfl | ht0
  · simp only [NNReal.coe_zero, mul_zero]; exact sq_nonneg _
  have hpos := sepN_pos h ht ht0
  set v₀ := log (sepN vL vR t)
  have hU := aemeasurable_logAngle h ht hpos
  have hbound : ∀ v ∈ Iic v₀, clockDensity (logAngle w vL vR ζ) v ≤ exp v₀ / 8 * exp v := by
    intro v hv
    have hv' : exp v ≤ sepN vL vR t := (le_log_iff_exp_le hpos).1 hv
    have h2 := mul_one_sub_mem_Icc (logAngle_mem_Icc h ht hv')
    have h1 : exp (2 * v) ≤ exp v₀ * exp v := by
      rw [← exp_add]; exact exp_le_exp.2 (by linarith [show v ≤ v₀ from hv])
    unfold clockDensity
    have := mul_le_mul h1 h2.2 h2.1 (by positivity)
    linarith
  have hnn : ∀ v ∈ Iic v₀, 0 ≤ clockDensity (logAngle w vL vR ζ) v := fun v hv =>
    div_nonneg (mul_nonneg (exp_pos _).le (mul_one_sub_mem_Icc (logAngle_mem_Icc h ht
      ((le_log_iff_exp_le hpos).1 hv))).1) zero_le_two
  have hint : IntegrableOn (clockDensity (logAngle w vL vR ζ)) (Iic v₀) := by
    refine ((integrableOn_exp_Iic v₀).const_mul (exp v₀ / 8)).mono' ?_ ?_
    · exact ((measurable_exp.comp (measurable_const.mul measurable_id)).aemeasurable.mul
        (hU.mul (aemeasurable_const.sub hU))).div_const _ |>.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Iic).2 (ae_of_all _ fun v hv => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn v hv)]
      exact hbound v hv
  have hle : clock (logAngle w vL vR ζ) v₀ ≤ exp v₀ * exp v₀ / 8 := by
    unfold clock
    calc ∫ v in Iic v₀, clockDensity (logAngle w vL vR ζ) v
        ≤ ∫ v in Iic v₀, exp v₀ / 8 * exp v :=
          setIntegral_mono_on hint ((integrableOn_exp_Iic v₀).const_mul _) measurableSet_Iic hbound
      _ = exp v₀ * exp v₀ / 8 := by rw [integral_const_mul, integral_exp_Iic]; ring
  rw [clock_logAngle_eq h ht ht0, exp_log hpos] at hle
  nlinarith

end Recovery

end TwoSeed

end Sec2

end InteractingSLE
