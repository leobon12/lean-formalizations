/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.CriticalExtension

/-!
# Auxiliary lemmas for the critical case of Aux. lemma 3

Packet PROVE-SEC2-TERM2.

* The regularized `x log x` (Specification p. 27, "apply Itô's formula to `F(x) = x log x`"):
  `xlogxReg ε` is `C²` on `ℝ` with second derivative `xlogxReg'' ε x = 1 / max x ε`, and equals
  `x log x` on `[ε, ∞)` (`xlogxReg_eq`), with derivative `1 + log x` there (`xlogxReg'_eq`). The
  stopping at `Q ≤ ε` of the source keeps the process in `[ε, M]`, where only these values enter.
* `intervalIntegral_le_of_forall_lt`, `intervalIntegrable_of_forall_lt`: passing an integral bound
  and integrability from `[q, u]`, `u < ρ`, to `[q, ρ]` (used at a localization time that equals
  the lifetime).
* `mem_of_forall_ratTime`: a condition checked at the rational times of `(q, ρ)` holds on `[q, ρ]`
  for a continuous function (the localizations test only rational times, for measurability).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-! ### The regularized `x log x` -/

/-- Second derivative of the regularized `x log x`: `1 / max x ε`. -/
def xlogxReg'' (ε x : ℝ) : ℝ := (max x ε)⁻¹

/-- First derivative of the regularized `x log x`. -/
def xlogxReg' (ε x : ℝ) : ℝ := 1 + Real.log ε + ∫ y in ε..x, xlogxReg'' ε y

/-- The regularized `x log x`: `C²`, equal to `x log x` on `[ε, ∞)`. -/
def xlogxReg (ε x : ℝ) : ℝ := ε * Real.log ε + ∫ y in ε..x, xlogxReg' ε y

variable {ε : ℝ}

theorem continuous_xlogxReg'' (hε : 0 < ε) : Continuous (xlogxReg'' ε) :=
  (continuous_id.max continuous_const).inv₀ fun x => (lt_of_lt_of_le hε (le_max_right x ε)).ne'

theorem xlogxReg''_pos (hε : 0 < ε) (x : ℝ) : 0 < xlogxReg'' ε x :=
  inv_pos.2 (lt_of_lt_of_le hε (le_max_right _ _))

theorem xlogxReg''_eq {x : ℝ} (hx : ε ≤ x) : xlogxReg'' ε x = x⁻¹ := by
  rw [xlogxReg'', max_eq_left hx]

theorem hasDerivAt_xlogxReg' (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (xlogxReg' ε) (xlogxReg'' ε x) x :=
  ((continuous_xlogxReg'' hε).integral_hasStrictDerivAt ε x).hasDerivAt.const_add _

theorem continuous_xlogxReg' (hε : 0 < ε) : Continuous (xlogxReg' ε) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_xlogxReg' hε x).continuousAt

theorem hasDerivAt_xlogxReg (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (xlogxReg ε) (xlogxReg' ε x) x :=
  ((continuous_xlogxReg' hε).integral_hasStrictDerivAt ε x).hasDerivAt.const_add _

theorem continuous_xlogxReg (hε : 0 < ε) : Continuous (xlogxReg ε) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_xlogxReg hε x).continuousAt

theorem xlogxReg'_eq (hε : 0 < ε) {x : ℝ} (hx : ε ≤ x) : xlogxReg' ε x = 1 + Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le hε hx
  have hcongr : ∫ y in ε..x, xlogxReg'' ε y = ∫ y in ε..x, y⁻¹ := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hx] at hy
    exact xlogxReg''_eq hy.1
  rw [xlogxReg', hcongr, integral_inv_of_pos hε hx0, Real.log_div hx0.ne' hε.ne']
  ring

theorem xlogxReg_eq (hε : 0 < ε) {x : ℝ} (hx : ε ≤ x) : xlogxReg ε x = x * Real.log x := by
  have hcongr : ∫ y in ε..x, xlogxReg' ε y = ∫ y in ε..x, (Real.log y + 1) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hx] at hy
    rw [xlogxReg'_eq hε hy.1]
    ring
  have hderiv : ∀ y ∈ uIcc ε x, HasDerivAt (fun y => y * Real.log y) (Real.log y + 1) y :=
    fun y hy => by
      rw [uIcc_of_le hx] at hy
      exact Real.hasDerivAt_mul_log (lt_of_lt_of_le hε hy.1).ne'
  have hint : IntervalIntegrable (fun y => Real.log y + 1) volume ε x := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (Real.continuousOn_log.mono fun y hy => ?_).add continuousOn_const
    rw [uIcc_of_le hx] at hy
    exact (lt_of_lt_of_le hε hy.1).ne'
  rw [xlogxReg, hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The clamp of `x` to `[ε, M]`. -/
def clampIcc (ε M x : ℝ) : ℝ := max ε (min M x)

theorem continuous_clampIcc (ε M : ℝ) : Continuous (clampIcc ε M) := by
  unfold clampIcc; fun_prop

theorem le_clampIcc (ε M x : ℝ) : ε ≤ clampIcc ε M x := le_max_left _ _

theorem clampIcc_le {ε M : ℝ} (hεM : ε ≤ M) (x : ℝ) : clampIcc ε M x ≤ M :=
  max_le hεM (min_le_left _ _)

theorem clampIcc_eq {ε M x : ℝ} (h1 : ε ≤ x) (h2 : x ≤ M) : clampIcc ε M x = x := by
  rw [clampIcc, min_eq_right h2, max_eq_right h1]

/-- `|x log x| ≤ M log M + 1` on `(0, M]`, `M ≥ 1`. -/
theorem abs_mul_log_le {M x : ℝ} (hM : 1 ≤ M) (hx : 0 < x) (hxM : x ≤ M) :
    |x * Real.log x| ≤ M * Real.log M + 1 := by
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hMl : 0 ≤ M * Real.log M := mul_nonneg (by linarith) hlogM
  rcases le_or_gt 1 x with h1 | h1
  · have hl : 0 ≤ Real.log x := Real.log_nonneg h1
    rw [abs_of_nonneg (mul_nonneg hx.le hl)]
    have := mul_le_mul hxM (Real.log_le_log hx hxM) hl (by linarith)
    linarith
  · have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le h1.le
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hx.le hl)]
    have h2 := Real.one_sub_inv_le_log_of_pos hx
    have h3 : x * (1 - x⁻¹) ≤ x * Real.log x := mul_le_mul_of_nonneg_left h2 hx.le
    have h4 : x * (1 - x⁻¹) = x - 1 := by field_simp
    linarith

/-- The regularized `x log x` of a clamped value is bounded by `M log M + 1`. -/
theorem abs_xlogxReg_clampIcc_le (hε : 0 < ε) {M : ℝ} (hεM : ε ≤ M) (hM : 1 ≤ M) (x : ℝ) :
    |xlogxReg ε (clampIcc ε M x)| ≤ M * Real.log M + 1 := by
  rw [xlogxReg_eq hε (le_clampIcc ε M x)]
  exact abs_mul_log_le hM (lt_of_lt_of_le hε (le_clampIcc ε M x)) (clampIcc_le hεM x)

/-! ### From `[q, u]`, `u < ρ`, to `[q, ρ]` -/

/-- An integral bound on every `[q, u]` with `u < ρ` passes to `[q, ρ]`. -/
theorem intervalIntegral_le_of_forall_lt {g : ℝ → ℝ} {q ρ : ℝ} (hqρ : q ≤ ρ)
    (hg : IntervalIntegrable g volume q ρ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ u, q ≤ u → u < ρ → ∫ x in q..u, g x ≤ K) : ∫ x in q..ρ, g x ≤ K := by
  rcases eq_or_lt_of_le hqρ with rfl | hlt
  · simpa using hK
  have hcont : ContinuousOn (fun u => ∫ x in q..u, g x) (uIcc q ρ) :=
    intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  rw [uIcc_of_le hqρ] at hcont
  have hW : ContinuousWithinAt (fun u => ∫ x in q..u, g x) (Ico q ρ) ρ :=
    (hcont ρ ⟨hqρ, le_rfl⟩).mono Ico_subset_Icc_self
  have hcl : ρ ∈ closure (Ico q ρ) := by
    rw [closure_Ico hlt.ne]; exact ⟨hqρ, le_rfl⟩
  have hmem := hW.mem_closure_image hcl
  have hsub : (fun u => ∫ x in q..u, g x) '' Ico q ρ ⊆ Iic K := by
    rintro _ ⟨u, hu, rfl⟩; exact h u hu.1 hu.2
  exact closure_minimal hsub isClosed_Iic hmem

/-- Integrability on every `[q, u]`, `u < ρ`, with a uniform bound on `∫ |g|`, gives
integrability on `[q, ρ]`. -/
theorem intervalIntegrable_of_forall_lt {g : ℝ → ℝ} {q ρ : ℝ} (hqρ : q < ρ)
    (hg : ∀ u, q ≤ u → u < ρ → IntervalIntegrable g volume q u) {K : ℝ}
    (h : ∀ u, q ≤ u → u < ρ → ∫ x in q..u, |g x| ≤ K) : IntervalIntegrable g volume q ρ := by
  set b : ℕ → ℝ := fun k => ρ - (ρ - q) / (k + 2) with hb
  have hb1 : ∀ k : ℕ, q ≤ b k := fun k => by
    have : (ρ - q) / (k + 2) ≤ ρ - q := div_le_self (by linarith) (by norm_cast; omega)
    simp only [hb]; linarith
  have hb2 : ∀ k : ℕ, b k < ρ := fun k => by
    have : 0 < (ρ - q) / (k + 2) := div_pos (by linarith) (by positivity)
    simp only [hb]; linarith
  have hlim : Tendsto b atTop (𝓝 ρ) := by
    have : Tendsto (fun k : ℕ => (ρ - q) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa [hb] using (tendsto_const_nhds (x := ρ)).sub this
  have hint : IntegrableOn g (Ioc q ρ) volume := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded (l := atTop) (a := fun _ => q)
      (b := b) (I := K) (fun k => ?_) tendsto_const_nhds hlim (Eventually.of_forall fun k => ?_)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hb1 k)).1 (hg _ (hb1 k) (hb2 k))
    · have := h _ (hb1 k) (hb2 k)
      rw [intervalIntegral.integral_of_le (hb1 k)] at this
      simpa only [Real.norm_eq_abs] using this
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hqρ.le).2 hint

/-! ### Conditions at rational times -/

/-- Every point of `[q, ρ]` is a limit of rational times in `(q, ρ)`. -/
theorem mem_closure_ratTimes {q ρ u : ℝ≥0} (hqρ : q < ρ) (hu : u ∈ Icc q ρ) :
    u ∈ closure {s : ℝ≥0 | ∃ r : ℚ, s = ratTime r ∧ q < s ∧ s < ρ} := by
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have hqρ' : (q : ℝ) < ρ := hqρ
  have hu1 : (q : ℝ) ≤ u := hu.1
  have hu2 : (u : ℝ) ≤ ρ := hu.2
  have hlt : max (q : ℝ) (u - δ) < min (ρ : ℝ) (u + δ) := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hqρ', by linarith⟩, by linarith, by linarith⟩
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
  have hqr : (q : ℝ) < r := (le_max_left _ _).trans_lt hr1
  have hr0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg q).trans hqr.le
  refine ⟨ratTime r, ⟨r, rfl, ?_, ?_⟩, ?_⟩
  · rw [← NNReal.coe_lt_coe, coe_ratTime_of_nonneg hr0]; exact hqr
  · rw [← NNReal.coe_lt_coe, coe_ratTime_of_nonneg hr0]
    exact hr2.trans_le (min_le_left _ _)
  · rw [NNReal.dist_eq, coe_ratTime_of_nonneg hr0, abs_sub_lt_iff]
    constructor <;> linarith [le_max_right (q : ℝ) (u - δ), min_le_right (ρ : ℝ) (u + δ)]

/-- A closed condition on a continuous function, checked at the rational times of `(q, ρ)`, holds
on `[q, ρ]`. -/
theorem mem_of_forall_ratTime {g : ℝ≥0 → ℝ} {q ρ u : ℝ≥0} (hqρ : q < ρ) (hu : u ∈ Icc q ρ)
    (hg : ContinuousWithinAt g (Icc q ρ) u) {C : Set ℝ} (hC : IsClosed C)
    (h : ∀ r : ℚ, q < ratTime r → ratTime r < ρ → g (ratTime r) ∈ C) : g u ∈ C := by
  set S := {s : ℝ≥0 | ∃ r : ℚ, s = ratTime r ∧ q < s ∧ s < ρ}
  have hS : S ⊆ Icc q ρ := by
    rintro _ ⟨r, rfl, h1, h2⟩; exact ⟨h1.le, h2.le⟩
  have hmem := (hg.mono hS).mem_closure_image (mem_closure_ratTimes hqρ hu)
  refine closure_minimal ?_ hC hmem
  rintro _ ⟨s, ⟨r, rfl, h1, h2⟩, rfl⟩
  exact h r h1 h2

end Sec2

end InteractingSLE
