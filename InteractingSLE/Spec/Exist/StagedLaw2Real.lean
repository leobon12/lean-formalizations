/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Spec.Exist.StagedLaw2Flow

/-!
# The real forward flow at one time: shape of the alive set and monotonicity

Packet PROVE-STAGEDLAW2. For a continuous driver `W` with `W 0 = 0` and a time `T ≥ 0`, the real points alive at
`T` (`∃ u, IsForwardSol W y T u`) and the real flow `y ↦ Re f_T(y)` have the structure used to read the records
`recR`, `recL` and the threshold events of `ExplState.launch` by countable operations (`IsRealFlow`):

* `0` is never alive; on `(0, ∞)` the alive set is an up-set containing all large points, on `(−∞, 0)` a down-set
  containing all very negative points;
* on alive points the flow keeps the sign, is strictly increasing, continuous (along alive points) and unbounded.

The negative half is the positive half of the reflected flow `W ↦ −W`, `y ↦ −y` (`IsRealFlow` is symmetric by
definition). Reused: QuantumZipper's `RS.exists_isForwardSol_of_lt` (monotonicity of aliveness), `SwallowReal`
(swallowing times, positivity, order, monotone uncentered flow, reflection), `RealPoints` (Grönwall).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper

/-! ### The abstract structure -/

/-- **One half of the real flow structure**: on `(0, ∞)`, the alive set `A` is an up-set containing all large points
and avoiding `0`, and the flow `f` is positive, strictly increasing, continuous along alive points and unbounded. -/
def IsRealHalf (A : ℝ → Prop) (f : ℝ → ℝ) : Prop :=
  ¬ A 0 ∧ (∀ q y, 0 < q → q < y → A q → A y) ∧ (∃ M, ∀ y, M ≤ y → A y) ∧
    (∀ y, 0 < y → A y → 0 < f y) ∧ (∀ x y, 0 < x → x < y → A x → A y → f x < f y) ∧
    (∀ x, 0 < x → A x → ∀ ε > 0, ∃ η > 0, ∀ y, A y → |y - x| < η → |f y - f x| < ε) ∧
    (∀ M, ∃ N, ∀ y, N ≤ y → A y → M ≤ f y)

/-- **The real flow structure**: both halves (the negative half read through `y ↦ −y`). -/
def IsRealFlow (A : ℝ → Prop) (f : ℝ → ℝ) : Prop :=
  IsRealHalf A f ∧ IsRealHalf (fun y => A (-y)) (fun y => -f (-y))

theorem IsRealFlow.reflect {A : ℝ → Prop} {f : ℝ → ℝ} (h : IsRealFlow A f) :
    IsRealFlow (fun y => A (-y)) (fun y => -f (-y)) := by
  refine ⟨h.2, ?_⟩
  simpa only [neg_neg] using h.1

/-! ### The Loewner flow has this structure -/

section Loewner

variable {W : ℝ → ℝ}

/-- A bound for the driver on `[0, T]`. -/
theorem exists_abs_driver_le (hW : Continuous W) (T : ℝ) : ∃ B, 0 ≤ B ∧ ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := W) (s := Icc (0 : ℝ) T) hW.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun s hs => (Real.norm_eq_abs _ ▸ hC s hs).trans (le_max_left _ _)⟩

/-- The uncentered real flow does not decrease: `Re f_s(y) ≥ y − W_s` while `y > 0` is alive. -/
theorem sub_le_re_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {y s : ℝ} (hy : 0 < y) (hs : 0 ≤ s)
    {v : ℝ → ℂ} (hv : IsForwardSol W (y : ℂ) s v) : y - W s ≤ (fwdMap W s y).re := by
  have hm := re_add_monotoneOn hW hW0 hy hs hv ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  beta_reduce at hm
  rw [FwdHolo.sol_zero hv hs, hW0] at hm
  rw [fwdMap_eq_of_isForwardSol hW hv ⟨hs, le_rfl⟩]
  simp only [Complex.ofReal_zero, sub_zero, Complex.ofReal_re, add_zero] at hm
  linarith

/-- **The positive half of the real Loewner flow.** -/
theorem isRealHalf_fwd (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    IsRealHalf (fun y : ℝ => ∃ u, IsForwardSol W (y : ℂ) T u) (fun y => (fwdMap W T y).re) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_driver_le hW T
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    have h := hu.2 0 ⟨le_rfl, hT⟩
    rw [intervalIntegral.integral_same, add_zero, hW0] at h
    exact h.1 (by rw [h.2]; simp)
  · rintro q y hq hqy ⟨u, hu⟩
    exact RS.exists_isForwardSol_of_lt hW hT (by rw [hW0]; exact hq) hqy hu
  · refine ⟨B + 1, fun y hy => ?_⟩
    have hy0 : 0 < y := by linarith
    by_contra hdead
    obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hW hW0 hy0 hT hdead
    have hlim := (Complex.continuous_re.tendsto _).comp (tendsto_fwdMap_of_realSwallowAt hW hW0 hy0 hsw)
    rw [Complex.zero_re] at hlim
    have hev : ∀ᶠ s in 𝓝[<] σ, 1 ≤ (fwdMap W s y).re := by
      filter_upwards [Ioo_mem_nhdsLT hσ.1] with s hs
      obtain ⟨v, hv⟩ := hsw.2.1 s ⟨hs.1.le, hs.2⟩
      have h1 := sub_le_re_of_isForwardSol hW hW0 hy0 hs.1.le hv
      have h2 := hB s ⟨hs.1.le, hs.2.le.trans hσ.2⟩
      linarith [abs_le.1 h2]
    have := ge_of_tendsto hlim hev
    linarith
  · rintro y hy ⟨u, hu⟩
    exact re_fwdMap_pos hW hW0 hy hu ⟨hT, le_rfl⟩
  · rintro x y hx hxy ⟨v, hv⟩ ⟨w, hw⟩
    show (fwdMap W T x).re < (fwdMap W T y).re
    rw [fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hw ⟨hT, le_rfl⟩]
    exact re_lt_of_isForwardSol hW hW0 hx hxy hv hw T ⟨hT, le_rfl⟩
  · rintro x - ⟨u, hu⟩ ε hε
    obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hu
    set E := Real.exp (2 / δ ^ 2 * T) with hE
    have hE0 : 0 < E := Real.exp_pos _
    refine ⟨min (δ / E) (ε / E), lt_min (by positivity) (by positivity), fun y ⟨v, hv⟩ hyx => ?_⟩
    have hyx' : ‖(y : ℂ) - x‖ = |y - x| := by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hzp : ‖(y : ℂ) - x‖ * E < δ := by
      rw [hyx']
      calc |y - x| * E < δ / E * E := by gcongr; exact hyx.trans_le (min_le_left _ _)
        _ = δ := by field_simp
    have h := norm_sub_le_of_isForwardSol hW hu hv hδ hT le_rfl hlow hzp T ⟨hT, le_rfl⟩
    show |(fwdMap W T y).re - (fwdMap W T x).re| < ε
    rw [fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hu ⟨hT, le_rfl⟩,
      ← Complex.sub_re]
    calc |(v T - u T).re| ≤ ‖v T - u T‖ := Complex.abs_re_le_norm _
      _ ≤ ‖(y : ℂ) - x‖ * E := h
      _ < ε / E * E := by rw [hyx']; gcongr; exact hyx.trans_le (min_le_right _ _)
      _ = ε := by field_simp
  · intro M
    refine ⟨max (M + B + 1) 1, fun y hy ⟨v, hv⟩ => ?_⟩
    have hy1 := (le_max_left _ _).trans hy
    have h1 := sub_le_re_of_isForwardSol hW hW0 (by linarith [(le_max_right (M + B + 1) 1).trans hy]) hT hv
    have h2 := hB T ⟨hT, le_rfl⟩
    show M ≤ (fwdMap W T y).re
    linarith [abs_le.1 h2]

/-- Reflection of the alive predicate. -/
theorem alive_neg_iff (W : ℝ → ℝ) (T y : ℝ) :
    (∃ u, IsForwardSol (-W) ((y : ℝ) : ℂ) T u) ↔ ∃ u, IsForwardSol W ((-y : ℝ) : ℂ) T u := by
  have h := exists_isForwardSol_neg_iff (W := W) (x := -y) (T := T)
  rw [neg_neg] at h
  exact h

/-- **The real Loewner flow has the real flow structure.** -/
theorem isRealFlow_fwd (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    IsRealFlow (fun y : ℝ => ∃ u, IsForwardSol W (y : ℂ) T u) (fun y => (fwdMap W T y).re) := by
  refine ⟨isRealHalf_fwd hW hW0 hT, ?_⟩
  have h := isRealHalf_fwd (W := -W) hW.neg (by simp [hW0]) hT
  have eA : (fun y : ℝ => ∃ u, IsForwardSol (-W) (y : ℂ) T u) =
      fun y : ℝ => ∃ u, IsForwardSol W ((-y : ℝ) : ℂ) T u := funext fun y => propext (alive_neg_iff W T y)
  have ef : (fun y : ℝ => (fwdMap (-W) T y).re) = fun y : ℝ => -(fwdMap W T ((-y : ℝ) : ℂ)).re := by
    funext y
    have := F1.fwdMap_reflect_ofReal W hT (-y)
    rw [neg_neg] at this
    rw [this, Complex.neg_re]
  rw [eA, ef] at h
  exact h

/-- The forward map sends real points to real points (junk values included). -/
theorem im_fwdMap_ofReal (W : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : (fwdMap W T (x : ℂ)).im = 0 := by
  have h := F1.fwdMap_conj_self_ofReal W hT x
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

theorem fwdMap_ofReal_eq (W : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    fwdMap W T (x : ℂ) = ((fwdMap W T (x : ℂ)).re : ℂ) :=
  Complex.ext (by simp) (by simp [im_fwdMap_ofReal W hT x])

end Loewner

end StagedLaw

end Exist

end InteractingSLE
