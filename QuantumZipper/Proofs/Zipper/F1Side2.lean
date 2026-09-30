import QuantumZipper.Proofs.Zipper.F1Side
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# F1d input (b): the real forward flow is order preserving

E-branch node F1d. `QuantumZipper/Proofs/Zipper/F1Side.lean` reduces the side-image identity to
the existence of the two one-sided limits of `x ↦ (fwdMap W t x).re` at `0`. This file and
`F1Side3.lean` prove that existence:

1. `im_eq_zero_of_isForwardSol_ofReal`: a forward solution started at a real point is real-valued
   (conjugation is a symmetry of the forward flow, and solutions are unique);
2. `sub_ne_zero_of_isForwardSol_lt`: two forward solutions started at real points `x < y` never
   meet on `[0,T]`. The difference `w = u₂ − u₁` satisfies the linear integral equation
   `w t = w 0 + ∫_0^t k s · w s ds` with `k s = −2/(u₁ s · u₂ s)`, whose solution is
   `w t = w 0 · exp(∫_0^t k)`; since `w 0 = y − x ≠ 0` and `exp` never vanishes, `w` never
   vanishes. (Grönwall-type uniqueness of the linear equation, via mathlib's
   `ODE_solution_unique_of_mem_Icc_right`.)
3. `isForwardSol_lt_of_lt`: the real forward flow is strictly order preserving — the intermediate
   value theorem, applied to the difference of the real parts, upgrades non-meeting to `<`.

The paper (Sheffield, arXiv:1012.4797, §5.4, p. 72) only says "by symmetry"; the real-flow
monotonicity used here is the standard fact that distinct real points are never identified by a
Loewner flow (cf. Kemppainen, *Schramm–Loewner Evolution*, Prop. 5.2, p. 80, on the same
monotonicity in `x`), and is proved here directly ("own elementary proof", steps 1–3).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology ENNReal ComplexConjugate NNReal

namespace QuantumZipper
namespace F1

/-! ## Step 1: solutions started at a real point are real-valued -/

/-- A forward solution started at a real point takes real values (conjugation is a symmetry of
the forward flow and solutions are unique, `isForwardSol_conj` + `isForwardSol_unique_gronwall`). -/
theorem im_eq_zero_of_isForwardSol_ofReal {W : ℝ → ℝ} {T x : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) {t : ℝ} (ht : t ∈ Icc 0 T) : (u t).im = 0 := by
  have huc : IsForwardSol W (x : ℂ) T fun s => conj (u s) := by
    simpa using isForwardSol_conj hu
  have h : conj (u t) = u t := isForwardSol_unique_gronwall huc hu ht
  have h2 : -(u t).im = (u t).im := by simpa using congrArg Complex.im h
  linarith

/-! ## Step 2: solutions from different real starting points never meet -/

/-- **Distinct real starting points give solutions that never meet.** If `u₁` solves the forward
flow from the real point `x` and `u₂` from the real point `y > x` on `[0,T]`, then
`u₁ t ≠ u₂ t` for every `t ∈ [0,T]`. The difference `w = u₂ − u₁` satisfies the linear integral
equation `w t = w 0 + ∫_0^t k s · w s ds` with `k s = −2/(u₁ s · u₂ s)`; comparison with its
explicit solution `w 0 · exp(∫_0^t k)` (mathlib's `ODE_solution_unique_of_mem_Icc_right` for the
Lipschitz vector field `y ↦ k t · y`, whose Lipschitz constant is bounded by `2/(c₁c₂)` on the
compact interval) shows `w t ≠ 0`. -/
theorem sub_ne_zero_of_isForwardSol_lt {W : ℝ → ℝ} {T x y : ℝ} (hT : 0 ≤ T) (hxy : x < y)
    {u₁ u₂ : ℝ → ℂ} (h₁ : IsForwardSol W (x : ℂ) T u₁) (h₂ : IsForwardSol W (y : ℂ) T u₂) :
    ∀ t ∈ Icc (0 : ℝ) T, u₁ t ≠ u₂ t := by
  obtain ⟨c₁, hc₁, hb₁⟩ := exists_pos_le_norm_of_isForwardSol h₁ hT
  obtain ⟨c₂, hc₂, hb₂⟩ := exists_pos_le_norm_of_isForwardSol h₂ hT
  set k : ℝ → ℂ := fun s => -2 / (u₁ s * u₂ s) with hk
  have hne : ∀ s ∈ Icc (0 : ℝ) T, u₁ s * u₂ s ≠ 0 :=
    fun s hs => mul_ne_zero (h₁.2 s hs).1 (h₂.2 s hs).1
  have hkc : ContinuousOn k (Icc 0 T) :=
    continuousOn_const.div (h₁.1.mul h₂.1) hne
  have hkcw : ContinuousOn (fun s => k s * (u₂ s - u₁ s)) (Icc 0 T) :=
    hkc.mul (h₂.1.sub h₁.1)
  -- the integral equation of the difference
  have hkint : ∀ s ∈ Icc (0 : ℝ) T, k s * (u₂ s - u₁ s) = (2 : ℂ) / u₂ s - 2 / u₁ s := by
    intro s hs
    have h1s : u₁ s ≠ 0 := (h₁.2 s hs).1
    have h2s : u₂ s ≠ 0 := (h₂.2 s hs).1
    rw [hk]
    field_simp [h1s, h2s]
    ring
  have hwk : ∀ t ∈ Icc (0 : ℝ) T,
      u₂ t - u₁ t = (u₂ 0 - u₁ 0) + ∫ s in (0 : ℝ)..t, k s * (u₂ s - u₁ s) := by
    intro t ht
    have hint1 : IntervalIntegrable (fun s => (2 : ℂ) / u₁ s) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact (continuousOn_const.div h₁.1 fun s hs => (h₁.2 s hs).1).mono
        (Icc_subset_Icc_right ht.2)
    have hint2 : IntervalIntegrable (fun s => (2 : ℂ) / u₂ s) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact (continuousOn_const.div h₂.1 fun s hs => (h₂.2 s hs).1).mono
        (Icc_subset_Icc_right ht.2)
    have hsub : (∫ s in (0 : ℝ)..t, k s * (u₂ s - u₁ s))
        = (∫ s in (0 : ℝ)..t, (2 : ℂ) / u₂ s) - ∫ s in (0 : ℝ)..t, (2 : ℂ) / u₁ s := by
      rw [← intervalIntegral.integral_sub hint2 hint1]
      refine intervalIntegral.integral_congr fun s hs => hkint s ?_
      rw [uIcc_of_le ht.1] at hs
      exact Icc_subset_Icc_right ht.2 hs
    rw [(h₁.2 t ht).2, (h₂.2 t ht).2, isForwardSol_zero h₁ hT, isForwardSol_zero h₂ hT, hsub]
    ring
  -- derivative of the difference
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ => u₂ τ - u₁ τ) (k t * (u₂ t - u₁ t)) (Icc 0 T) t := by
    intro t ht
    have hint : IntervalIntegrable (fun s => k s * (u₂ s - u₁ s)) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact hkcw.mono (Icc_subset_Icc_right ht.2)
    have hfact : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
    have hFTC : HasDerivWithinAt (fun τ => ∫ s in (0 : ℝ)..τ, k s * (u₂ s - u₁ s))
        (k t * (u₂ t - u₁ t)) (Icc 0 T) t :=
      intervalIntegral.integral_hasDerivWithinAt_right hint
        (hkcw.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hkcw t ht)
    have hev : (fun s => u₂ s - u₁ s) =ᶠ[𝓝[Icc (0 : ℝ) T] t]
        fun τ => (u₂ 0 - u₁ 0) + ∫ s in (0 : ℝ)..τ, k s * (u₂ s - u₁ s) :=
      eventually_nhdsWithin_of_forall fun y hy => hwk y hy
    exact (hFTC.const_add (u₂ 0 - u₁ 0)).congr_of_eventuallyEq hev (hwk t ht)
  -- derivative of the exponential factor
  have hKderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun τ => ∫ s in (0 : ℝ)..τ, k s) (k t) (Icc 0 T) t := by
    intro t ht
    have hint : IntervalIntegrable k volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact hkc.mono (Icc_subset_Icc_right ht.2)
    have hfact : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right hint
      (hkc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hkc t ht)
  -- the explicit solution of the linear equation
  set g : ℝ → ℂ := fun t => (u₂ 0 - u₁ 0) * Complex.exp (∫ s in (0 : ℝ)..t, k s) with hg
  have hgderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt g (k t * g t) (Icc 0 T) t := by
    intro t ht
    have hexp : HasDerivWithinAt (fun τ => Complex.exp (∫ s in (0 : ℝ)..τ, k s))
        (Complex.exp (∫ s in (0 : ℝ)..t, k s) * k t) (Icc 0 T) t :=
      (Complex.hasDerivAt_exp _).comp_hasDerivWithinAt t (hKderiv t ht)
    have := hexp.const_mul (u₂ 0 - u₁ 0)
    simpa [hg, mul_comm, mul_left_comm, mul_assoc] using this
  have hlip : ∀ t ∈ Ico (0 : ℝ) T,
      LipschitzOnWith (⟨2 / (c₁ * c₂), by positivity⟩ : ℝ≥0) (fun y : ℂ => k t * y) univ := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
    have hprod : c₁ * c₂ ≤ ‖u₁ t‖ * ‖u₂ t‖ :=
      mul_le_mul (hb₁ t htI) (hb₂ t htI) hc₂.le (norm_nonneg _)
    have hkbd : ‖k t‖ ≤ 2 / (c₁ * c₂) := by
      have hpos : 0 < ‖u₁ t‖ * ‖u₂ t‖ := lt_of_lt_of_le (mul_pos hc₁ hc₂) hprod
      rw [hk, norm_div, norm_neg, show ‖(2 : ℂ)‖ = 2 from by norm_num, norm_mul]
      exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hc₁ hc₂) hprod
    refine LipschitzOnWith.of_dist_le_mul fun y₁ _ y₂ _ => ?_
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right hkbd (norm_nonneg _)
  have huniq := ODE_solution_unique_of_mem_Icc_right (a := (0 : ℝ)) (b := T)
    (v := fun (t : ℝ) (y : ℂ) => k t * y) (s := fun (_ : ℝ) => (univ : Set ℂ))
    (K := (⟨2 / (c₁ * c₂), by positivity⟩ : ℝ≥0))
    hlip (h₂.1.sub h₁.1)
    (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t _ => mem_univ _)
    (fun t ht => (hgderiv t ht).continuousWithinAt)
    (fun t ht => (hgderiv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t _ => mem_univ _)
    (by
      show u₂ 0 - u₁ 0 = (u₂ 0 - u₁ 0) * Complex.exp (∫ s in (0 : ℝ)..0, k s)
      rw [intervalIntegral.integral_same, Complex.exp_zero, mul_one])
  have hw0 : u₂ 0 - u₁ 0 = ((y - x : ℝ) : ℂ) := by
    rw [isForwardSol_zero h₂ hT, isForwardSol_zero h₁ hT]
    push_cast
    ring
  have hw0ne : ((y - x : ℝ) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact sub_ne_zero.2 hxy.ne'
  intro t ht
  have hne0 : (u₂ - u₁) t ≠ 0 := by
    rw [huniq ht, hg, hw0]
    exact mul_ne_zero hw0ne (Complex.exp_ne_zero _)
  exact fun h => hne0 (show u₂ t - u₁ t = 0 from sub_eq_zero.2 h.symm)

/-! ## Step 3: the real forward flow is order preserving -/

/-- **Order preservation.** If `x < y` are real and `u₁`, `u₂` solve the forward flow from `x`
and `y` on `[0,T]`, then `(u₁ t).re < (u₂ t).re` for every `t ∈ [0,T]`: the difference of the real
parts is continuous, is positive at `0` and never vanishes (`sub_ne_zero_of_isForwardSol_lt`),
hence is positive everywhere by the intermediate value theorem. -/
theorem isForwardSol_lt_of_lt {W : ℝ → ℝ} {T x y : ℝ} (hT : 0 ≤ T) (hxy : x < y)
    {u₁ u₂ : ℝ → ℂ} (h₁ : IsForwardSol W (x : ℂ) T u₁) (h₂ : IsForwardSol W (y : ℂ) T u₂) :
    ∀ t ∈ Icc (0 : ℝ) T, (u₁ t).re < (u₂ t).re := by
  intro t ht
  have hne := sub_ne_zero_of_isForwardSol_lt hT hxy h₁ h₂
  by_contra hcon
  push Not at hcon
  have hd : ContinuousOn (fun s => (u₂ s).re - (u₁ s).re) (Icc 0 t) :=
    ((Complex.continuous_re.comp_continuousOn h₂.1).sub
      (Complex.continuous_re.comp_continuousOn h₁.1)).mono (Icc_subset_Icc_right ht.2)
  have h0val : (u₂ 0).re - (u₁ 0).re = y - x := by
    rw [isForwardSol_zero h₂ hT, isForwardSol_zero h₁ hT]
    simp
  have hmem : (0 : ℝ) ∈ Icc ((fun s => (u₂ s).re - (u₁ s).re) t)
      ((fun s => (u₂ s).re - (u₁ s).re) 0) := by
    simp only [h0val]
    exact ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 hd hmem
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  have h1re := im_eq_zero_of_isForwardSol_ofReal h₁ hsI
  have h2re := im_eq_zero_of_isForwardSol_ofReal h₂ hsI
  have hsre : (u₁ s).re = (u₂ s).re := by linarith
  have hsu : u₁ s = u₂ s := Complex.ext hsre (by rw [h1re, h2re])
  exact hne s hsI hsu

end F1
end QuantumZipper
