/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.Bessel.Comparison
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Regularized Bessel equations

Packet PROVE-BESSEL. For `c ≥ 0`, `ε > 0` and a continuous path `w : ℝ → ℝ`, the regularized
Bessel equation

  `X t = x + w t + ∫₀ᵗ c / max (X s) ε ds`,   `t ≥ 0`,

has a unique continuous solution `regSol c ε x w`. The drift `regDrift c ε = c / max · ε` is
bounded by `c / ε`, Lipschitz with constant `c / ε²`, nonincreasing in the space variable and
nonincreasing in `ε`; it equals `c / x` for `x ≥ ε`. By the comparison principle
(`le_of_sub_eq_integral`) the solutions increase as `ε` decreases (`regSol_le_regSol`).

Existence is Picard–Lindelöf for `v = X - w`, `v' = regDrift c ε (v + w t)` on each `[0, T]`
(Mathlib `IsPicardLindelof`), glued by uniqueness (`ODE_solution_unique`); the construction follows
`QuantumZipper.ClockInt.exists_realUnc_sol` (real-valued instead of complex-valued).
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

noncomputable section

namespace InteractingSLE

namespace Bessel

/-! ### The regularized drift -/

/-- The regularized Bessel drift `c / max x ε`. -/
def regDrift (c ε x : ℝ) : ℝ := c / max x ε

variable {c ε x : ℝ}

theorem regDrift_nonneg (hc : 0 ≤ c) (hε : 0 < ε) (x : ℝ) : 0 ≤ regDrift c ε x :=
  div_nonneg hc (hε.le.trans (le_max_right _ _))

theorem regDrift_le (hc : 0 ≤ c) (hε : 0 < ε) (x : ℝ) : regDrift c ε x ≤ c / ε :=
  div_le_div_of_nonneg_left hc hε (le_max_right _ _)

theorem abs_regDrift_le (hc : 0 ≤ c) (hε : 0 < ε) (x : ℝ) : |regDrift c ε x| ≤ c / ε := by
  rw [abs_of_nonneg (regDrift_nonneg hc hε x)]
  exact regDrift_le hc hε x

theorem regDrift_of_le (hx : ε ≤ x) : regDrift c ε x = c / x := by
  rw [regDrift, max_eq_left hx]

theorem regDrift_of_le' (hx : x ≤ ε) : regDrift c ε x = c / ε := by
  rw [regDrift, max_eq_right hx]

/-- The drift is nonincreasing in the space variable. -/
theorem regDrift_anti (hc : 0 ≤ c) (hε : 0 < ε) {x y : ℝ} (hxy : x ≤ y) :
    regDrift c ε y ≤ regDrift c ε x :=
  div_le_div_of_nonneg_left hc (hε.trans_le (le_max_right _ _)) (max_le_max hxy le_rfl)

/-- The drift is nonincreasing in the regularization parameter. -/
theorem regDrift_le_of_le (hc : 0 ≤ c) {ε' : ℝ} (hε' : 0 < ε') (hεε : ε' ≤ ε) (x : ℝ) :
    regDrift c ε x ≤ regDrift c ε' x :=
  div_le_div_of_nonneg_left hc (hε'.trans_le (le_max_right _ _)) (max_le_max le_rfl hεε)

/-- The drift is nondecreasing in the coefficient. -/
theorem regDrift_mono_coeff {c' : ℝ} (hcc : c ≤ c') (hε : 0 < ε) (x : ℝ) :
    regDrift c ε x ≤ regDrift c' ε x :=
  div_le_div_of_nonneg_right hcc (hε.le.trans (le_max_right _ _))

theorem lipschitzWith_regDrift (hc : 0 ≤ c) (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (c / ε ^ 2)) (regDrift c ε) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
  set mx := max x ε
  set my := max y ε
  have hmx : ε ≤ mx := le_max_right _ _
  have hmy : ε ≤ my := le_max_right _ _
  have hmx0 : 0 < mx := hε.trans_le hmx
  have hmy0 : 0 < my := hε.trans_le hmy
  have hm : |my - mx| ≤ |x - y| := by
    rw [abs_sub_comm]
    exact abs_max_sub_max_le_abs _ _ _
  have hprod : ε ^ 2 ≤ mx * my := by
    rw [sq]; exact mul_le_mul hmx hmy hε.le hmx0.le
  simp only [regDrift]
  rw [div_sub_div _ _ hmx0.ne' hmy0.ne', abs_div, abs_of_pos (mul_pos hmx0 hmy0)]
  have hnum : |c * my - mx * c| = c * |my - mx| := by
    rw [show c * my - mx * c = c * (my - mx) by ring, abs_mul, abs_of_nonneg hc]
  rw [hnum, div_le_iff₀ (mul_pos hmx0 hmy0)]
  calc c * |my - mx| ≤ c * |x - y| := mul_le_mul_of_nonneg_left hm hc
    _ = c / ε ^ 2 * |x - y| * ε ^ 2 := by field_simp
    _ ≤ c / ε ^ 2 * |x - y| * (mx * my) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

theorem continuous_regDrift (hc : 0 ≤ c) (hε : 0 < ε) : Continuous (regDrift c ε) :=
  (lipschitzWith_regDrift hc hε).continuous

/-! ### Existence of the regularized solution -/

variable {w : ℝ → ℝ}

/-- A derivative within `[a, b]` at `t ∈ [a, b)` is a derivative within `[t, ∞)`. -/
theorem hasDerivWithinAt_Ici_of_Icc {f : ℝ → ℝ} {f' a b t : ℝ}
    (h : HasDerivWithinAt f f' (Icc a b) t) (ht : t ∈ Ico a b) :
    HasDerivWithinAt f f' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))

theorem lipschitzWith_regDrift_shift (hc : 0 ≤ c) (hε : 0 < ε) (a : ℝ) :
    LipschitzWith (Real.toNNReal (c / ε ^ 2)) (fun v => regDrift c ε (v + a)) := by
  refine LipschitzWith.of_dist_le_mul fun v u => ?_
  have := (lipschitzWith_regDrift hc hε).dist_le_mul (v + a) (u + a)
  rwa [dist_add_right] at this

/-- Global existence for `v' = regDrift c ε (v + w t)`, `v 0 = x`, on `[0, T]`. -/
theorem exists_regUnc_sol (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T)
    (x : ℝ) :
    ∃ v : ℝ → ℝ, v 0 = x ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (regDrift c ε (v t + w t)) (Icc 0 T) t := by
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  set t0 : Icc (0 : ℝ) T := ⟨0, h0mem⟩ with ht0_def
  have ht0_coe : (t0 : ℝ) = 0 := rfl
  have hf : IsPicardLindelof (fun t v => regDrift c ε (v + w t)) t0 x
      (Real.toNNReal (c / ε * T)) 0 (Real.toNNReal (c / ε)) (Real.toNNReal (c / ε ^ 2)) := by
    refine ⟨fun t _ => (lipschitzWith_regDrift_shift hc hε _).lipschitzOnWith,
      fun v _ => ?_, ?_, ?_⟩
    · exact ((continuous_regDrift hc hε).comp (continuous_const.add hw)).continuousOn
    · intro t _ v _
      rw [Real.coe_toNNReal _ (by positivity), Real.norm_eq_abs]
      exact abs_regDrift_le hc hε _
    · simp only [ht0_coe, sub_zero, NNReal.coe_zero, max_eq_left hT,
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ c / ε),
        Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ c / ε * T), le_refl]
  have hx : x ∈ Metric.closedBall x ((0 : ℝ≥0) : ℝ) := Metric.mem_closedBall_self (le_refl _)
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_⟩
  · show α.compProj (t0 : ℝ) = x
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
      x ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

open Classical in
/-- The solution `v = X - w` of the regularized equation (junk `0` unless `w` is continuous,
`0 ≤ c` and `0 < ε`). -/
def regUnc (c ε x : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  if h : Continuous w ∧ 0 ≤ c ∧ 0 < ε then
    Classical.choose (exists_regUnc_sol h.1 h.2.1 h.2.2 (le_max_right t 0) x) t else 0

/-- **The regularized Bessel solution** `X = x + w + ∫₀^· c / max X ε` (`regSol_eq`). -/
def regSol (c ε x : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := regUnc c ε x w t + w t

theorem regUnc_eq_of_sol (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε) {T : ℝ}
    {V : ℝ → ℝ} (hV0 : V 0 = x)
    (hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (regDrift c ε (V t + w t)) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, regUnc c ε x w t = V t := by
  intro t ht
  rw [regUnc, dite_eq_left_of_eq_true (eq_true ⟨hw, hc, hε⟩)]
  obtain ⟨hv0, hvd⟩ := Classical.choose_spec (exists_regUnc_sol hw hc hε (le_max_right t 0) x)
  set v := Classical.choose (exists_regUnc_sol hw hc hε (le_max_right t 0) x) with hvdef
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 (max t 0) := Icc_subset_Icc_right (le_max_left _ _)
  have hsubT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have key := ODE_solution_unique (v := fun s v => regDrift c ε (v + w s))
    (fun s => lipschitzWith_regDrift_shift hc hε _) (f := v) (g := V) (a := 0) (b := t)
    (fun s hs => (hvd s (hsub hs)).continuousWithinAt.mono hsub)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc ((hvd s (hsub (Ico_subset_Icc_self hs))).mono hsub)
      hs)
    (fun s hs => (hV s (hsubT hs)).continuousWithinAt.mono hsubT)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc ((hV s (hsubT (Ico_subset_Icc_self hs))).mono hsubT)
      hs)
    (by rw [hv0, hV0])
  exact key ⟨ht.1, le_rfl⟩

theorem regUnc_zero (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε) (x : ℝ) :
    regUnc c ε x w 0 = x := by
  rw [regUnc, dite_eq_left_of_eq_true (eq_true ⟨hw, hc, hε⟩)]
  exact (Classical.choose_spec (exists_regUnc_sol hw hc hε (le_max_right 0 0) x)).1

theorem regUnc_hasDerivWithinAt (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε) {T : ℝ}
    (hT : 0 ≤ T) (x : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (regUnc c ε x w) (regDrift c ε (regSol c ε x w t)) (Icc 0 T) t := by
  obtain ⟨v, hv0, hvd⟩ := exists_regUnc_sol hw hc hε hT x
  have heq := regUnc_eq_of_sol hw hc hε hv0 hvd
  intro t ht
  have e : regSol c ε x w t = v t + w t := by rw [regSol, heq t ht]
  rw [e]
  exact (hvd t ht).congr_of_mem heq ht

theorem continuousOn_regUnc (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε) {T : ℝ}
    (hT : 0 ≤ T) (x : ℝ) : ContinuousOn (regUnc c ε x w) (Icc 0 T) := fun t ht =>
  (regUnc_hasDerivWithinAt hw hc hε hT x t ht).continuousWithinAt

theorem continuousOn_regSol (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε) {T : ℝ}
    (hT : 0 ≤ T) (x : ℝ) : ContinuousOn (regSol c ε x w) (Icc 0 T) :=
  (continuousOn_regUnc hw hc hε hT x).add hw.continuousOn

/-- The regularized solution is continuous on `[0, ∞)`. -/
theorem continuousOn_regSol_Ici (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε) (x : ℝ) :
    ContinuousOn (regSol c ε x w) (Ici 0) := by
  intro t ht
  have h := continuousOn_regSol hw hc hε (T := t + 1) (by linarith [mem_Ici.1 ht]) x
  have hmem : Icc (0 : ℝ) (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (h t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- **Integral equation** of the regularized solution. -/
theorem regSol_eq (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    regSol c ε x w t = x + w t + ∫ s in (0 : ℝ)..t, regDrift c ε (regSol c ε x w s) := by
  have hcont : ContinuousOn (regUnc c ε x w) (Icc 0 t) := continuousOn_regUnc hw hc hε ht x
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt (regUnc c ε x w) (regDrift c ε (regSol c ε x w s)) s := fun s hs =>
    (regUnc_hasDerivWithinAt hw hc hε ht x s (Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  have hint : IntervalIntegrable (fun s => regDrift c ε (regSol c ε x w s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact (continuous_regDrift hc hε).comp_continuousOn (continuousOn_regSol hw hc hε ht x)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  rw [regUnc_zero hw hc hε] at key
  rw [regSol, key]
  ring

theorem intervalIntegrable_regDrift_regSol (hw : Continuous w) (hc : 0 ≤ c) (hε : 0 < ε)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => regDrift c ε (regSol c ε x w s)) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht]
  exact (continuous_regDrift hc hε).comp_continuousOn (continuousOn_regSol hw hc hε ht x)

/-! ### Monotonicity -/

/-- **Comparison of regularized solutions.** If `c ≤ c'`, `x ≤ x'` and `ε' ≤ ε`, then the
regularized solution with `(c, ε, x)` lies below the one with `(c', ε', x')`. -/
theorem regSol_le_regSol (hw : Continuous w) (hc : 0 ≤ c) {c' ε' x' : ℝ} (hcc : c ≤ c')
    (hε' : 0 < ε') (hεε : ε' ≤ ε) (hxx : x ≤ x') {t : ℝ} (ht : 0 ≤ t) :
    regSol c ε x w t ≤ regSol c' ε' x' w t := by
  have hε : 0 < ε := hε'.trans_le hεε
  have hc' : 0 ≤ c' := hc.trans hcc
  refine le_of_sub_eq_integral (T := t) (continuousOn_regSol hw hc hε ht x)
    (continuousOn_regSol hw hc' hε' ht x')
    (intervalIntegrable_regDrift_regSol hw hc hε x ht)
    (intervalIntegrable_regDrift_regSol hw hc' hε' x' ht) ?_ ?_ ?_ t ⟨ht, le_rfl⟩
  · rw [regSol_eq hw hc hε x le_rfl, regSol_eq hw hc' hε' x' le_rfl]
    simp [hxx]
  · intro s hs
    have hint := intervalIntegrable_regDrift_regSol hw hc hε x hs.1
    have hint' := intervalIntegrable_regDrift_regSol hw hc' hε' x' hs.1
    rw [regSol_eq hw hc hε x hs.1, regSol_eq hw hc' hε' x' hs.1,
      regSol_eq hw hc hε x le_rfl, regSol_eq hw hc' hε' x' le_rfl,
      intervalIntegral.integral_sub hint hint']
    simp only [intervalIntegral.integral_same, add_zero]
    ring
  · refine ae_of_all _ fun s _ hlt => ?_
    calc regDrift c ε (regSol c ε x w s) ≤ regDrift c ε (regSol c' ε' x' w s) :=
          regDrift_anti hc hε hlt.le
      _ ≤ regDrift c ε' (regSol c' ε' x' w s) := regDrift_le_of_le hc hε' hεε _
      _ ≤ regDrift c' ε' (regSol c' ε' x' w s) := regDrift_mono_coeff hcc hε' _

end Bessel

end InteractingSLE
