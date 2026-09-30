import QuantumZipper.Proofs.Loewner.RealLine
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Holomorphic extension of the reverse Loewner map at non-swallowed real points

Blueprint task A2-ext (`blueprint/E_BRANCH_BLUEPRINT.md` §3).

We extend the reverse Loewner map `revMap W T` across the real points not swallowed by time
`T`. The extension is `revMapExt W T z`: the time-`T` value of the (unique) solution of the
reverse integral equation `u_s = z - W_s - ∫₀ˢ 2/u` that avoids `0` on `[0,T]` (junk `0` if
there is none). We prove:

* `revMapExt` agrees with `revMap` on `ℍ` and with `realRevMap` at non-swallowed real points,
  and commutes with complex conjugation everywhere;
* near every real point `x` with a real solution on `[0,T]`, complex solutions exist on a ball
  (by Picard–Lindelöf for a box-truncated field, plus Grönwall);
* `revMapExt` is holomorphic there, with derivative `exp (∫₀ᵀ 2/u²)`, which is real and positive
  at real points.

Main result: `exists_revMapExt_extension` (and the blueprint-shaped `revMap_extension_A2ext`).
Neither `W 0 = 0` nor compactness of `J` is needed.
-/

noncomputable section

open Complex Filter MeasureTheory intervalIntegral Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace RevMapExtension

/-- `u` solves the reverse centered Loewner equation from the complex point `z` on `[0,T]`,
avoiding `0`: `u_s = z - W_s - ∫₀ˢ 2/u` and `u_s ≠ 0`. -/
def IsCRevSol (W : ℝ → ℝ) (z : ℂ) (T : ℝ) (u : ℝ → ℂ) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ∀ s ∈ Icc 0 T, u s ≠ 0 ∧ u s = z - W s - ∫ r in (0 : ℝ)..s, 2 / u r

open Classical in
/-- The extended reverse flow map: time-`T` value of the solution avoiding `0` (junk `0`). -/
def revMapExt (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  if h : ∃ u, IsCRevSol W z T u then (Classical.choose h) T else 0

variable {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}

/-! ### Basic facts on solutions -/

theorem isCRevSol_restrict (h : IsCRevSol W z T u) {t : ℝ} (htT : t ≤ T) :
    IsCRevSol W z t u :=
  ⟨h.1.mono (Icc_subset_Icc_right htT), fun s hs => h.2 s (Icc_subset_Icc_right htT hs)⟩

theorem isCRevSol_zero (h : IsCRevSol W z T u) (hT : 0 ≤ T) : u 0 = z - W 0 := by
  have := (h.2 0 ⟨le_rfl, hT⟩).2
  rw [this, integral_same, sub_zero]

theorem isCRevSol_of_isReverseSol (h : IsReverseSol W z T u) : IsCRevSol W z T u :=
  ⟨h.1, fun s hs => ⟨fun h0 => by
    have := (h.2 s hs).1
    rw [h0] at this; simp at this, (h.2 s hs).2⟩⟩

theorem isCRevSol_ofReal {x : ℝ} {w : ℝ → ℝ} (h : IsRealRevSol W x T w) :
    IsCRevSol W x T (fun s => (w s : ℂ)) := by
  refine ⟨continuous_ofReal.comp_continuousOn h.1, fun s hs =>
    ⟨ofReal_ne_zero.2 (h.2 s hs).1, ?_⟩⟩
  have e : (fun r => (2 : ℂ) / (w r : ℂ)) = fun r => ((2 / w r : ℝ) : ℂ) := by
    funext r; push_cast; rfl
  simp only
  rw [e, intervalIntegral.integral_ofReal]
  conv_lhs => rw [(h.2 s hs).2]
  push_cast; ring

theorem isCRevSol_conj (h : IsCRevSol W z T u) :
    IsCRevSol W (conj z) T (fun s => conj (u s)) := by
  refine ⟨Complex.continuous_conj.comp_continuousOn h.1, fun s hs => ⟨?_, ?_⟩⟩
  · exact (map_ne_zero _).2 (h.2 s hs).1
  · have e : (fun r => (2 : ℂ) / conj (u r)) = fun r => conj (2 / u r) := by
      funext r; rw [map_div₀, map_ofNat]
    simp only
    rw [e, intervalIntegral_conj]
    conv_lhs => rw [(h.2 s hs).2]
    simp only [map_sub, Complex.conj_ofReal]

theorem isCRevSol_hasDerivWithinAt (h : IsCRevSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s + (W s : ℂ)) (-2 / u t) (Icc (0 : ℝ) T) t := by
  obtain ⟨hcont, hprop⟩ := h
  have hgcont : ContinuousOn (fun s => (-2 : ℂ) / u s) (Icc (0 : ℝ) T) :=
    ContinuousOn.div continuousOn_const hcont fun s hs => (hprop s hs).1
  have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  have hsub : uIcc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2
  have hint : IntervalIntegrable (fun s => (-2 : ℂ) / u s) volume 0 t :=
    (hgcont.mono hsub).intervalIntegrable
  have hderiv0 : HasDerivWithinAt (fun r => ∫ x in (0 : ℝ)..r, (-2 : ℂ) / u x) (-2 / u t)
      (Icc (0 : ℝ) T) t :=
    integral_hasDerivWithinAt_right hint
      (hgcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hgcont t ht)
  have hderiv := hderiv0.const_add z
  have heq : ∀ s ∈ Icc (0 : ℝ) T,
      u s + (W s : ℂ) = z + ∫ x in (0 : ℝ)..s, (-2 : ℂ) / u x := by
    intro s hs
    have hus := (hprop s hs).2
    have hneg : (∫ x in (0 : ℝ)..s, (-2 : ℂ) / u x) = -∫ x in (0 : ℝ)..s, (2 : ℂ) / u x := by
      rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
    rw [hneg, hus]
    ring
  exact hderiv.congr_of_mem heq ht

/-- The difference of two solutions solves a linear equation. -/
theorem isCRevSol_sub_eq {z₁ z₂ : ℂ} {u₁ u₂ : ℝ → ℂ} (h₁ : IsCRevSol W z₁ T u₁)
    (h₂ : IsCRevSol W z₂ T u₂) (hT : 0 ≤ T) :
    u₂ T - u₁ T = (z₂ - z₁) * Complex.exp (∫ s in (0 : ℝ)..T, 2 / (u₂ s * u₁ s)) := by
  set a : ℝ → ℂ := fun s => 2 / (u₂ s * u₁ s) with ha
  have hacont : ContinuousOn a (Icc 0 T) :=
    continuousOn_const.div (h₂.1.mul h₁.1) fun s hs => mul_ne_zero (h₂.2 s hs).1 (h₁.2 s hs).1
  set A : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, a s with hA
  have hAder : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt A (a t) (Icc 0 T) t := by
    intro t ht
    have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
    have hsub : uIcc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := by
      rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2
    exact integral_hasDerivWithinAt_right ((hacont.mono hsub).intervalIntegrable)
      (hacont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hacont t ht)
  set E : ℝ → ℂ := fun t => ((u₂ t + (W t : ℂ)) - (u₁ t + (W t : ℂ))) * Complex.exp (-A t)
    with hE
  have hEder : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt E 0 (Icc 0 T) t := by
    intro t ht
    have h1 := ((isCRevSol_hasDerivWithinAt h₂ ht).sub
      (isCRevSol_hasDerivWithinAt h₁ ht)).mul (hAder t ht).neg.cexp
    have n1 := (h₂.2 t ht).1
    have n2 := (h₁.2 t ht).1
    have hval : (-2 / u₂ t - -2 / u₁ t) * Complex.exp (-A t) +
        ((u₂ t + (W t : ℂ)) - (u₁ t + (W t : ℂ))) * (Complex.exp (-A t) * -a t) = 0 := by
      simp only [ha]
      field_simp
      ring
    exact h1.congr_deriv hval
  have hconst := constant_of_has_deriv_right_zero
    (fun t ht => (hEder t ht).continuousWithinAt)
    (fun t ht => (hEder t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) T ⟨hT, le_rfl⟩
  have hE0 : E 0 = z₂ - z₁ := by
    simp only [hE, hA, integral_same, neg_zero, Complex.exp_zero, mul_one]
    rw [isCRevSol_zero h₂ hT, isCRevSol_zero h₁ hT]; ring
  have hET : E T = z₂ - z₁ := hconst.trans hE0
  have hexp : Complex.exp (-A T) * Complex.exp (A T) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc u₂ T - u₁ T = E T * Complex.exp (A T) := by
        simp only [hE]; linear_combination (-(u₂ T - u₁ T)) * hexp
    _ = (z₂ - z₁) * Complex.exp (∫ s in (0 : ℝ)..T, 2 / (u₂ s * u₁ s)) := by rw [hET]

theorem isCRevSol_unique {u₁ u₂ : ℝ → ℂ} (h₁ : IsCRevSol W z T u₁) (h₂ : IsCRevSol W z T u₂) :
    EqOn u₁ u₂ (Icc 0 T) := by
  intro s hs
  have := isCRevSol_sub_eq (isCRevSol_restrict h₁ hs.2) (isCRevSol_restrict h₂ hs.2) hs.1
  rw [sub_self, zero_mul, sub_eq_zero] at this
  exact this.symm

/-- Lipschitz dependence on the initial point, for solutions staying at distance `≥ c` from 0. -/
theorem norm_isCRevSol_sub_le {z₁ z₂ : ℂ} {u₁ u₂ : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (h₁ : IsCRevSol W z₁ T u₁) (h₂ : IsCRevSol W z₂ T u₂)
    (hb₁ : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u₁ s‖) (hb₂ : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u₂ s‖) :
    ∀ τ ∈ Icc (0 : ℝ) T, ‖u₂ τ - u₁ τ‖ ≤ ‖z₂ - z₁‖ * Real.exp (2 / c ^ 2 * T) := by
  intro τ hτ
  rw [isCRevSol_sub_eq (isCRevSol_restrict h₁ hτ.2) (isCRevSol_restrict h₂ hτ.2) hτ.1,
    norm_mul, Complex.norm_exp]
  gcongr
  refine (Complex.re_le_norm _).trans ?_
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 / c ^ 2)
    fun r hr => ?_).trans ?_
  · rw [uIoc_of_le hτ.1] at hr
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.trans hτ.2⟩
    rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have := mul_le_mul (hb₂ r hrT) (hb₁ r hrT) hc.le (norm_nonneg _)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  · rw [sub_zero, abs_of_nonneg hτ.1]
    exact mul_le_mul_of_nonneg_left hτ.2 (by positivity)

/-! ### The extended map -/

theorem revMapExt_eq (h : IsCRevSol W z T u) (hT : 0 ≤ T) : revMapExt W T z = u T := by
  have hex : ∃ u', IsCRevSol W z T u' := ⟨u, h⟩
  rw [revMapExt, dite_eq_left_of_eq_true (eq_true hex)]
  exact isCRevSol_unique (Classical.choose_spec hex) h ⟨hT, le_rfl⟩

theorem revMapExt_conj (hT : 0 ≤ T) (z : ℂ) :
    revMapExt W T (conj z) = conj (revMapExt W T z) := by
  by_cases hex : ∃ u, IsCRevSol W z T u
  · obtain ⟨u, hu⟩ := hex
    rw [revMapExt_eq (isCRevSol_conj hu) hT, revMapExt_eq hu hT]
  · have hex' : ¬ ∃ u, IsCRevSol W (conj z) T u := by
      rintro ⟨u, hu⟩
      apply hex
      have := isCRevSol_conj hu
      rw [Complex.conj_conj] at this
      exact ⟨_, this⟩
    unfold revMapExt
    rw [dite_eq_right_of_eq_false (eq_false hex'), dite_eq_right_of_eq_false (eq_false hex), map_zero]

theorem revMapExt_eq_revMap (hW : Continuous W) (hT : 0 ≤ T) (hz : 0 < z.im) :
    revMapExt W T z = revMap W T z := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT
  rw [revMapExt_eq (isCRevSol_of_isReverseSol hu) hT, revMap_eq W hW z hT le_rfl hu]

theorem revMapExt_ofReal (hW : Continuous W) (hT : 0 ≤ T) {x : ℝ} {w : ℝ → ℝ}
    (h : IsRealRevSol W x T w) : revMapExt W T x = realRevMap W T x := by
  rw [revMapExt_eq (isCRevSol_ofReal h) hT, RealLine.realRevMap_eq hW h hT le_rfl]

/-- Lipschitz bound for `revMapExt` between points with solutions bounded away from `0`. -/
theorem norm_revMapExt_sub_le (hT : 0 ≤ T) {z₁ z₂ : ℂ} {u₁ u₂ : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (h₁ : IsCRevSol W z₁ T u₁) (h₂ : IsCRevSol W z₂ T u₂)
    (hb₁ : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u₁ s‖) (hb₂ : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u₂ s‖) :
    ‖revMapExt W T z₂ - revMapExt W T z₁‖ ≤ ‖z₂ - z₁‖ * Real.exp (2 / c ^ 2 * T) := by
  rw [revMapExt_eq h₁ hT, revMapExt_eq h₂ hT]
  exact norm_isCRevSol_sub_le hc h₁ h₂ hb₁ hb₂ T ⟨hT, le_rfl⟩

/-! ### Holomorphy -/

/-- If all points of a ball around `z₀` have solutions staying at distance `≥ c` from `0`,
then `revMapExt W T` is complex differentiable at `z₀` with derivative `exp (∫₀ᵀ 2/u₀²)`. -/
theorem hasDerivAt_revMapExt (hT : 0 ≤ T) {z₀ : ℂ} {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (hgood : ∀ w ∈ Metric.ball z₀ ρ, ∃ u, IsCRevSol W w T u ∧ ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u s‖)
    {u₀ : ℝ → ℂ} (hu₀ : IsCRevSol W z₀ T u₀) :
    HasDerivAt (revMapExt W T) (Complex.exp (∫ s in (0 : ℝ)..T, 2 / (u₀ s) ^ 2)) z₀ := by
  choose! U hU hUc using hgood
  have hz₀ : z₀ ∈ Metric.ball z₀ ρ := Metric.mem_ball_self hρ
  have hU₀ : EqOn (U z₀) u₀ (Icc 0 T) := isCRevSol_unique (hU z₀ hz₀) hu₀
  have hc₀ : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u₀ s‖ := fun s hs => by
    rw [← hU₀ hs]; exact hUc z₀ hz₀ s hs
  set M := Real.exp (2 / c ^ 2 * T) with hM
  set K := 2 * M / c ^ 3 * T with hK
  have hint : ∀ w ∈ Metric.ball z₀ ρ,
      IntervalIntegrable (fun s => (2 : ℂ) / (U w s * u₀ s)) volume 0 T := by
    intro w hw
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact continuousOn_const.div ((hU w hw).1.mul hu₀.1)
      fun s hs => mul_ne_zero ((hU w hw).2 s hs).1 (hu₀.2 s hs).1
  have hint0 : IntervalIntegrable (fun s => (2 : ℂ) / (u₀ s * u₀ s)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact continuousOn_const.div (hu₀.1.mul hu₀.1)
      fun s hs => mul_ne_zero (hu₀.2 s hs).1 (hu₀.2 s hs).1
  have hlip : ∀ w ∈ Metric.ball z₀ ρ,
      ‖(∫ s in (0 : ℝ)..T, (2 : ℂ) / (U w s * u₀ s)) -
        ∫ s in (0 : ℝ)..T, (2 : ℂ) / (u₀ s * u₀ s)‖ ≤ K * ‖w - z₀‖ := by
    intro w hw
    rw [← intervalIntegral.integral_sub (hint w hw) hint0]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 2 * M / c ^ 3 * ‖w - z₀‖) fun s hs => ?_).trans_eq
      (by rw [sub_zero, abs_of_nonneg hT, hK]; ring)
    rw [uIoc_of_le hT] at hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
    have n1 : c ≤ ‖U w s‖ := hUc w hw s hsT
    have n2 : c ≤ ‖u₀ s‖ := hc₀ s hsT
    have p0 : U w s ≠ 0 := ((hU w hw).2 s hsT).1
    have q0 : u₀ s ≠ 0 := (hu₀.2 s hsT).1
    have hnum : ‖U w s - u₀ s‖ ≤ ‖w - z₀‖ * M :=
      norm_isCRevSol_sub_le hc hu₀ (hU w hw) hc₀ (hUc w hw) s hsT
    have hrw : 2 / (U w s * u₀ s) - 2 / (u₀ s * u₀ s)
        = 2 * (u₀ s - U w s) / (U w s * u₀ s * u₀ s) := by
      field_simp
    rw [hrw, norm_div, norm_mul, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num,
      norm_sub_rev]
    have hden : c * c * c ≤ ‖U w s‖ * ‖u₀ s‖ * ‖u₀ s‖ :=
      mul_le_mul (mul_le_mul n1 n2 hc.le (norm_nonneg _)) n2 hc.le (by positivity)
    calc 2 * ‖U w s - u₀ s‖ / (‖U w s‖ * ‖u₀ s‖ * ‖u₀ s‖)
        ≤ 2 * (‖w - z₀‖ * M) / (c * c * c) := by gcongr
      _ = 2 * M / c ^ 3 * ‖w - z₀‖ := by ring
  have hcont : Tendsto (fun w => ∫ s in (0 : ℝ)..T, (2 : ℂ) / (U w s * u₀ s)) (𝓝 z₀)
      (𝓝 (∫ s in (0 : ℝ)..T, (2 : ℂ) / (u₀ s * u₀ s))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg (by positivity) hT
    filter_upwards [Metric.ball_mem_nhds z₀ (show 0 < min ρ (ε / (K + 1)) by positivity)]
      with w hw
    rw [Metric.mem_ball, dist_eq_norm, lt_min_iff] at hw
    rw [dist_eq_norm]
    refine (hlip w (by rw [Metric.mem_ball, dist_eq_norm]; exact hw.1)).trans_lt ?_
    calc K * ‖w - z₀‖ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hw.2.le hK0
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have e : (∫ s in (0 : ℝ)..T, 2 / (u₀ s) ^ 2) = ∫ s in (0 : ℝ)..T, 2 / (u₀ s * u₀ s) := by
    simp only [sq]
  rw [e, hasDerivAt_iff_tendsto_slope]
  refine ((Complex.continuous_exp.tendsto _).comp hcont).mono_left nhdsWithin_le_nhds
    |>.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hρ), self_mem_nhdsWithin]
    with w hw hwne
  have hsub : w - z₀ ≠ 0 := sub_ne_zero.mpr hwne
  rw [slope_def_field, revMapExt_eq (hU w hw) hT, revMapExt_eq hu₀ hT,
    isCRevSol_sub_eq hu₀ (hU w hw) hT]
  simp only [Function.comp]
  field_simp

/-! ### Existence of complex solutions near a non-swallowed real point -/

private def clampR (lo hi y : ℝ) : ℝ := min (max y lo) hi

private theorem abs_clampR_sub_le (lo hi y₁ y₂ : ℝ) :
    |clampR lo hi y₁ - clampR lo hi y₂| ≤ |y₁ - y₂| := by
  unfold clampR
  refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le ?_ (by simp))
  refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le le_rfl (by simp))

private theorem clampR_mem {lo hi : ℝ} (h : lo ≤ hi) (y : ℝ) :
    lo ≤ clampR lo hi y ∧ clampR lo hi y ≤ hi :=
  ⟨le_min (le_max_right _ _) h, min_le_right _ _⟩

private theorem clampR_eq {lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) : clampR lo hi y = y := by
  unfold clampR; rw [max_eq_left h1, min_eq_left h2]

/-- Clamp to the closed box `[m - r, m + r] × [-r, r]`. -/
private def boxClamp (m r : ℝ) (y : ℂ) : ℂ :=
  (clampR (m - r) (m + r) y.re : ℂ) + (clampR (-r) r y.im : ℂ) * I

private theorem boxClamp_re (m r : ℝ) (y : ℂ) :
    (boxClamp m r y).re = clampR (m - r) (m + r) y.re := by simp [boxClamp]

private theorem boxClamp_im (m r : ℝ) (y : ℂ) :
    (boxClamp m r y).im = clampR (-r) r y.im := by simp [boxClamp]

private theorem boxClamp_eq {m r : ℝ} {y : ℂ} (hre : |y.re - m| ≤ r) (him : |y.im| ≤ r) :
    boxClamp m r y = y := by
  have h1 := abs_le.1 hre
  have h2 := abs_le.1 him
  apply Complex.ext
  · rw [boxClamp_re]; exact clampR_eq (by linarith) (by linarith)
  · rw [boxClamp_im]; exact clampR_eq (by linarith) (by linarith)

private theorem norm_le_norm_of_abs_le {a b : ℂ} (hre : |a.re| ≤ |b.re|)
    (him : |a.im| ≤ |b.im|) : ‖a‖ ≤ ‖b‖ := by
  have h1 : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    have e1 := sq_le_sq.2 hre
    have e2 := sq_le_sq.2 him
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

private theorem norm_boxClamp_sub_le (m r : ℝ) (y₁ y₂ : ℂ) :
    ‖boxClamp m r y₁ - boxClamp m r y₂‖ ≤ ‖y₁ - y₂‖ := by
  apply norm_le_norm_of_abs_le
  · rw [Complex.sub_re, Complex.sub_re, boxClamp_re, boxClamp_re]; exact abs_clampR_sub_le _ _ _ _
  · rw [Complex.sub_im, Complex.sub_im, boxClamp_im, boxClamp_im]; exact abs_clampR_sub_le _ _ _ _

private theorem norm_boxClamp_sub_center_le {m r : ℝ} (hr : 0 ≤ r) (y : ℂ) :
    ‖boxClamp m r y - (m : ℂ)‖ ≤ 2 * r := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im, boxClamp_re, boxClamp_im, ofReal_re, ofReal_im, sub_zero]
  have h1 := clampR_mem (show m - r ≤ m + r by linarith) y.re
  have h2 := clampR_mem (show -r ≤ r by linarith) y.im
  have e1 : |clampR (m - r) (m + r) y.re - m| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
  have e2 : |clampR (-r) r y.im| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

/-- Near a real point with a real solution on `[0,T]`, complex solutions exist on a ball and stay
at a uniform positive distance from `0`. -/
theorem exists_ball_isCRevSol (hW : Continuous W) (hT : 0 ≤ T) {x : ℝ} {w : ℝ → ℝ}
    (hw : IsRealRevSol W x T w) :
    ∃ c > 0, ∃ ρ > 0, ∀ z ∈ Metric.ball (x : ℂ) ρ,
      ∃ u, IsCRevSol W z T u ∧ ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u s‖ := by
  obtain ⟨c, hc, hcw⟩ := RealLine.exists_pos_le_abs_isRealRevSol hw hT
  set r := c / 4 with hr
  have hr0 : 0 < r := by positivity
  set m : ℝ → ℝ := fun s => w s + W s with hm
  have hmcont : ContinuousOn m (Icc 0 T) := hw.1.add hW.continuousOn
  set mC : ℝ → ℂ := fun s => (w s : ℂ) + (W s : ℂ) with hmC
  set F : ℝ → ℂ → ℂ := fun s y => -2 / (boxClamp (m s) r y - W s) with hF
  have hPfar : ∀ s ∈ Icc (0 : ℝ) T, ∀ y, c / 2 ≤ ‖boxClamp (m s) r y - W s‖ := by
    intro s hs y
    have h1 := norm_boxClamp_sub_center_le (m := m s) hr0.le y
    have h2 := hcw s hs
    have e : boxClamp (m s) r y - (W s : ℂ) = (w s : ℂ) + (boxClamp (m s) r y - (m s : ℂ)) := by
      simp only [hm]; push_cast; ring
    have h3 : ‖((w s : ℝ) : ℂ)‖ = |w s| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h4 := norm_sub_le ((w s : ℂ) + (boxClamp (m s) r y - (m s : ℂ)))
      (boxClamp (m s) r y - (m s : ℂ))
    rw [add_sub_cancel_right, ← e] at h4
    linarith
  set K : ℝ≥0 := ⟨2 / (c / 2) ^ 2, by positivity⟩ with hKdef
  have hFlip : ∀ s ∈ Icc (0 : ℝ) T, LipschitzWith K (F s) := by
    intro s hs
    apply LipschitzWith.of_dist_le_mul
    intro y₁ y₂
    rw [dist_eq_norm, dist_eq_norm]
    have h1 := RealLine.norm_neg_two_div_sub_le' (by positivity : 0 < c / 2) (hPfar s hs y₁)
      (hPfar s hs y₂)
    rw [show boxClamp (m s) r y₁ - (W s : ℂ) - (boxClamp (m s) r y₂ - W s) =
      boxClamp (m s) r y₁ - boxClamp (m s) r y₂ by ring] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (norm_boxClamp_sub_le _ _ _ _) (by positivity))
  have hFbd : ∀ s ∈ Icc (0 : ℝ) T, ∀ y, ‖F s y‖ ≤ 2 / (c / 2) := by
    intro s hs y
    have h1 := hPfar s hs y
    simp only [hF]
    rw [norm_div, show ‖(-2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h1
  have hFcont : ∀ y, ContinuousOn (fun s => F s y) (Icc 0 T) := by
    intro y
    have hP : ContinuousOn (fun s => boxClamp (m s) r y) (Icc 0 T) := by
      simp only [boxClamp, clampR]
      refine ContinuousOn.add ?_ continuousOn_const
      exact continuous_ofReal.comp_continuousOn
        (((continuous_const.max (continuous_id.sub continuous_const)).min
          (continuous_id.add continuous_const)).comp_continuousOn hmcont)
    exact continuousOn_const.div (hP.sub (continuous_ofReal.comp hW).continuousOn)
      fun s hs h0 => by have := hPfar s hs y; rw [h0, norm_zero] at this; linarith
  have hFm : ∀ s ∈ Icc (0 : ℝ) T, F s (mC s) = -2 / (w s : ℂ) := by
    intro s hs
    have hb : boxClamp (m s) r (mC s) = mC s := by
      apply boxClamp_eq
      · simp only [hmC, hm, add_re, ofReal_re, sub_self, abs_zero]; exact hr0.le
      · simp only [hmC, add_im, ofReal_im, add_zero, abs_zero]; exact hr0.le
    rw [show F s (mC s) = -2 / (boxClamp (m s) r (mC s) - W s) from rfl, hb]
    simp only [hmC, add_sub_cancel_right]
  set ρ := r / Real.exp (K * T) with hρ
  refine ⟨c / 2, by positivity, ρ, by positivity, fun z hz => ?_⟩
  have hpl : IsPicardLindelof F (⟨0, ⟨le_rfl, hT⟩⟩ : Icc (0 : ℝ) T) z
      ⟨2 / (c / 2) * T, mul_nonneg (by positivity) hT⟩ 0 ⟨2 / (c / 2), by positivity⟩ K := by
    refine ⟨fun s hs => (hFlip s hs).lipschitzOnWith, fun y _ => hFcont y,
      fun s hs y _ => hFbd s hs y, ?_⟩
    show 2 / (c / 2) * max (T - 0) (0 - 0) ≤ 2 / (c / 2) * T - 0
    rw [sub_zero, sub_zero, max_eq_left hT, sub_zero]
  obtain ⟨α, hα0, hαd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0' : α 0 = z := hα0
  have hαcont : ContinuousOn α (Icc 0 T) := fun s hs => (hαd s hs).continuousWithinAt
  -- Grönwall comparison with the real solution
  have hgd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => α s - mC s)
      (F s (α s) - F s (mC s)) (Icc 0 T) s := by
    intro s hs
    rw [hFm s hs]
    exact (hαd s hs).sub (RealLine.isRealRevSol_hasDerivWithinAt_ofReal hw hs)
  have hgc : ContinuousOn (fun s => α s - mC s) (Icc 0 T) :=
    fun s hs => (hgd s hs).continuousWithinAt
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖z - x‖) (K := K) (ε := 0)
    hgc (fun s hs => (hgd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (by
      apply le_of_eq
      simp only [hmC]
      rw [hα0', RealLine.isRealRevSol_zero hw hT]
      congr 1; push_cast; ring)
    (fun s hs => by
      rw [add_zero, ← dist_eq_norm, ← dist_eq_norm]
      exact (hFlip s (Ico_subset_Icc_self hs)).dist_le_mul _ _)
  have hzx : ‖z - x‖ * Real.exp (K * T) < r := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact (lt_div_iff₀ (Real.exp_pos _)).1 hz
  have hsmall : ∀ s ∈ Icc (0 : ℝ) T, ‖α s - mC s‖ ≤ r := by
    intro s hs
    have h1 := hgr s hs
    rw [gronwallBound_ε0, sub_zero] at h1
    have h2 : Real.exp (K * s) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 K.2)
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (z - x))
    linarith
  have hPα : ∀ s ∈ Icc (0 : ℝ) T, boxClamp (m s) r (α s) = α s := by
    intro s hs
    have h1 := hsmall s hs
    apply boxClamp_eq
    · have := (Complex.abs_re_le_norm (α s - mC s)).trans h1
      simpa [hmC, hm] using this
    · have := (Complex.abs_im_le_norm (α s - mC s)).trans h1
      simpa [hmC] using this
  set u : ℝ → ℂ := fun s => α s - W s with hu
  have hubd : ∀ s ∈ Icc (0 : ℝ) T, c / 2 ≤ ‖u s‖ := by
    intro s hs
    have := hPfar s hs (α s)
    rwa [hPα s hs] at this
  have hune : ∀ s ∈ Icc (0 : ℝ) T, u s ≠ 0 := by
    intro s hs h0
    have := hubd s hs
    rw [h0, norm_zero] at this
    linarith
  have hucont : ContinuousOn u (Icc 0 T) :=
    hαcont.sub (continuous_ofReal.comp hW).continuousOn
  have hderiv : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt α (-2 / u s) (Icc 0 T) s := by
    intro s hs
    have := hαd s hs
    have e : F s (α s) = -2 / u s := by
      simp only [hF, hu, hPα s hs]
    rwa [e] at this
  refine ⟨u, ⟨hucont, fun s hs => ⟨hune s hs, ?_⟩⟩, hubd⟩
  have hsubT : Icc (0 : ℝ) s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
  have hlocal : ∀ q ∈ Ioo (0 : ℝ) s, HasDerivWithinAt α (-2 / u q) (Ioi q) q := by
    intro q hq
    have hq' : q ∈ Ico (0 : ℝ) T := ⟨hq.1.le, lt_of_lt_of_le hq.2 hs.2⟩
    exact ((hderiv q (Ico_subset_Icc_self hq')).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hq')).mono Ioi_subset_Ici_self
  have hint : IntervalIntegrable (fun q => (-2 : ℂ) / u q) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs.1]
    exact continuousOn_const.div (hucont.mono hsubT) (fun q hq => hune q (hsubT hq))
  have hFTC : ∫ q in (0 : ℝ)..s, (-2 : ℂ) / u q = α s - α 0 :=
    integral_eq_sub_of_hasDeriv_right_of_le hs.1 (hαcont.mono hsubT) hlocal hint
  have hneg : (∫ q in (0 : ℝ)..s, (-2 : ℂ) / u q) = -∫ q in (0 : ℝ)..s, (2 : ℂ) / u q := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext q; ring
  show α s - W s = z - W s - ∫ q in (0 : ℝ)..s, 2 / u q
  linear_combination -hFTC + hneg + hα0'

/-! ### Main result -/

/-- **A2-ext.** Holomorphic extension of the reverse Loewner map across the real points not
swallowed by time `t`. The extension is the explicit function `revMapExt W t`. -/
theorem exists_revMapExt_extension (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) (J : Set ℝ)
    (hJ : ∀ x ∈ J, ENNReal.ofReal t < realHitTime W x) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x ∈ J, (x : ℂ) ∈ U) ∧ (∀ z ∈ U, conj z ∈ U) ∧
      DifferentiableOn ℂ (revMapExt W t) U ∧
      (∀ z : ℂ, 0 < z.im → revMapExt W t z = revMap W t z) ∧
      (∀ z : ℂ, revMapExt W t (conj z) = conj (revMapExt W t z)) ∧
      (∀ x ∈ J, revMapExt W t x = realRevMap W t x) ∧
      (∀ x ∈ J, deriv (revMapExt W t) x =
        (Real.exp (∫ s in (0 : ℝ)..t, 2 / (realRevMap W s x) ^ 2) : ℂ)) ∧
      (∀ x ∈ J, 0 < (deriv (revMapExt W t) x).re ∧ (deriv (revMapExt W t) x).im = 0) := by
  have hloc : ∀ x ∈ J, ∃ c > 0, ∃ ρ > 0, ∀ z ∈ Metric.ball (x : ℂ) ρ,
      ∃ u, IsCRevSol W z t u ∧ ∀ s ∈ Icc (0 : ℝ) t, c ≤ ‖u s‖ := fun x hx => by
    obtain ⟨w, hw⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hJ x hx)
    exact exists_ball_isCRevSol hW ht hw
  choose! c hc ρ hρ hgood using hloc
  -- the derivative at real points
  have hderivJ : ∀ x ∈ J, deriv (revMapExt W t) x =
      (Real.exp (∫ s in (0 : ℝ)..t, 2 / (realRevMap W s x) ^ 2) : ℂ) := by
    intro x hx
    obtain ⟨w, hw⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hJ x hx)
    rw [(hasDerivAt_revMapExt ht (hρ x hx) (hc x hx) (hgood x hx) (isCRevSol_ofReal hw)).deriv]
    have e1 : (fun s => (2 : ℂ) / ((w s : ℂ)) ^ 2) = fun s => ((2 / (w s) ^ 2 : ℝ) : ℂ) := by
      funext s; push_cast; rfl
    have e2 : (∫ s in (0 : ℝ)..t, 2 / (w s) ^ 2) =
        ∫ s in (0 : ℝ)..t, 2 / (realRevMap W s x) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht] at hs
      simp only [RealLine.realRevMap_eq hW hw hs.1 hs.2]
    rw [e1, intervalIntegral.integral_ofReal, e2, Complex.ofReal_exp]
  refine ⟨⋃ x ∈ J, Metric.ball (x : ℂ) (ρ x), isOpen_biUnion fun _ _ => Metric.isOpen_ball,
    fun x hx => mem_biUnion hx (Metric.mem_ball_self (hρ x hx)), ?_, ?_,
    fun z hz => revMapExt_eq_revMap hW ht hz, revMapExt_conj ht, ?_, hderivJ, ?_⟩
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hz
    refine mem_biUnion hx ?_
    rw [Metric.mem_ball, ← Complex.conj_ofReal, dist_conj_conj]
    exact hzx
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 hz
    have hε : 0 < ρ x - dist z x := by rw [Metric.mem_ball] at hzx; linarith
    have hsub : Metric.ball z (ρ x - dist z x) ⊆ Metric.ball (x : ℂ) (ρ x) :=
      Metric.ball_subset_ball' (by linarith)
    obtain ⟨u₀, hu₀, -⟩ := hgood x hx z hzx
    exact (hasDerivAt_revMapExt ht hε (hc x hx) (fun w hw => hgood x hx w (hsub hw))
      hu₀).differentiableAt.differentiableWithinAt
  · intro x hx
    obtain ⟨w, hw⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hJ x hx)
    exact revMapExt_ofReal hW ht hw
  · intro x hx
    rw [hderivJ x hx, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨Real.exp_pos _, rfl⟩

end RevMapExtension

end QuantumZipper
