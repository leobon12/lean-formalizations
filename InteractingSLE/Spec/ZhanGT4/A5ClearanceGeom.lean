/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceProb
import InteractingSLE.Spec.ZhanGT4.NoClusterLift
import InteractingSLE.Spec.ZhanGT4.NoCluster
import InteractingSLE.Spec.Zhan.AvoidHeight
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# Protected-ray clearance, VI: the deterministic argument

Packet PROVE-ZHAN-CLEAR (added here). Let `w` be a continuous driver and `V^R` a right force point that never meets it,
`Z = V^R − w > 0`, `s_t = ∫₀ᵗ Z⁻²`. Suppose that for every `A ∈ ℕ` there is `t₀` with `2A e^{−(s_t − s_{t₀})/3} < Z_t`
for all `t ≥ t₀` (`ae_exists_clearTime`). Then for every `M` there is `δ > 0` such that no hull point comes within
`δ` of `[p_R, M]` (`exists_clearance_right`).

For `z ∈ ℍ` put `w_t(z) = f_t(z) − Z_t` (`= g_t(z) − V^R_t`): it solves `w' = 2/(w + Z) − 2/Z = −2w/(Z(w + Z))`, so
while `|w| ≤ Z/2`, `d|w|²/dt ≤ −(8/9)|w|²/Z²` (`inner_gap_le`). Hence the fence `|w|² ≤ A² e^{−2(s − s_{t₀})/3}`,
which stays below `Z²/4` by the hypothesis, cannot be crossed (`normSq_le_of_barrier`, Mathlib's
`image_le_of_deriv_right_lt_deriv_boundary'`), `|f_t(z)| ≥ Z_t/2` after `t₀`, the swallowing clock stays bounded,
and `z` is never swallowed (`not_mem_fwdHull_of_barrier`). Before `t₀`, points near `[p_R, M]` follow the real flows
of `[p_R, M]` (Grönwall, `RealPoints`), which stay right of `V^R` and contract towards it (`re_sub_le_of_isForwardSol`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A5Clear

open QuantumZipper

/-! ### The contraction of `w` near the force point -/

/-- **The contraction inequality**: for `a = x + iy` with `|a|² ≤ Z²/4`,
`x Re(2/(a + Z) − 2/Z) + y Im(2/(a + Z) − 2/Z) ≤ −(4/9) |a|²/Z²`. -/
theorem inner_gap_le {a : ℂ} {Z : ℝ} (hZ : 0 < Z) (ha : normSq a ≤ Z ^ 2 / 4) :
    a.re * (2 / (a + Z) - 2 / Z).re + a.im * (2 / (a + Z) - 2 / Z).im ≤ -(4 / 9) * normSq a / Z ^ 2 := by
  set x := a.re with hx
  set y := a.im with hy
  have hn : normSq a = x ^ 2 + y ^ 2 := by rw [normSq_apply]; ring
  rw [hn] at ha ⊢
  have hxZ : -(Z / 2) ≤ x := by nlinarith [sq_nonneg y, sq_nonneg (x + Z / 2)]
  have hpos : 0 < x + Z := by linarith
  set D := (x + Z) ^ 2 + y ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hDa : normSq (a + (Z : ℂ)) = D := by
    rw [normSq_apply]; simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]; rw [hD, ← hx, ← hy]; ring
  have h1 : (2 / (a + Z) - 2 / Z).re = 2 * (x + Z) / D - 2 / Z := by
    rw [sub_re, div_re, div_re, hDa]
    simp only [re_ofNat, im_ofNat, add_re, ofReal_re, add_im, ofReal_im, add_zero, zero_mul, normSq_ofReal,
      ← hx]
    field_simp
    ring
  have h2 : (2 / (a + Z) - 2 / Z).im = -2 * y / D := by
    rw [sub_im, div_im, div_im, hDa]
    simp only [re_ofNat, im_ofNat, add_re, ofReal_re, add_im, ofReal_im, add_zero, zero_mul, normSq_ofReal,
      ← hy, mul_zero, zero_div, sub_zero]
    ring
  rw [h1, h2]
  have key : x * (2 * (x + Z) / D - 2 / Z) + y * (-2 * y / D) = -(2 * (x ^ 2 + y ^ 2) * (x + Z)) / (Z * D) := by
    field_simp
    ring
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  have h9 : 2 * D ≤ 9 * Z * (x + Z) := by nlinarith
  have hs : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h9 (mul_nonneg hs hZ.le)]

/-! ### The fence -/

/-- **The fence**: on `[t₀, t]`, `|f_r(z) − Z_r|² ≤ A² e^{−2(s_r − s_{t₀})/3}` as long as this level stays below
`Z²/4` (which the hypothesis `2A e^{−(s_r − s_{t₀})/3} < Z_r` guarantees). -/
theorem normSq_le_of_barrier {W : ℝ → ℝ} {pR : ℝ} {Zr clk : ℝ → ℝ} (hZpos : ∀ r, 0 < Zr r) {t : ℝ}
    (huR : IsForwardSol W pR t (fun s => ((Zr s : ℝ) : ℂ))) (hclk : ∀ r, HasDerivAt clk ((Zr r ^ 2)⁻¹) r)
    {z : ℂ} {v : ℝ → ℂ} (hv : IsForwardSol W z t v) {t₀ A : ℝ} (ht₀ : 0 ≤ t₀)
    (hA0 : 0 < A) (hA : normSq (v t₀ - Zr t₀) < A ^ 2)
    (hbar : ∀ r, t₀ ≤ r → 2 * A * Real.exp (-(clk r - clk t₀) / 3) < Zr r) :
    ∀ r ∈ Icc t₀ t, normSq (v r - Zr r) ≤ A ^ 2 * Real.exp (-(2 / 3) * (clk r - clk t₀)) := by
  set g : ℝ → ℂ := fun s => v s - ((Zr s : ℝ) : ℂ) with hg
  set g' : ℝ → ℂ := fun s => 2 / v s - 2 / ((Zr s : ℝ) : ℂ) with hg'
  have hgd : ∀ r ∈ Icc (0 : ℝ) t, HasDerivWithinAt g (g' r) (Icc 0 t) r := by
    intro r hr
    have h3 := (FwdHolo.hasDerivWithinAt_shift hv hr).sub (FwdHolo.hasDerivWithinAt_shift huR hr)
    exact h3.congr (fun s _ => by simp only [hg, Pi.sub_apply]; ring) (by simp only [hg, Pi.sub_apply]; ring)
  set f : ℝ → ℝ := fun s => normSq (g s) with hf
  set f' : ℝ → ℝ := fun s => 2 * ((g s).re * (g' s).re + (g s).im * (g' s).im) with hf'
  have hfd : ∀ r ∈ Icc (0 : ℝ) t, HasDerivWithinAt f (f' r) (Icc 0 t) r := by
    intro r hr
    have hre := reCLM.hasFDerivAt.comp_hasDerivWithinAt r (hgd r hr)
    have him := imCLM.hasFDerivAt.comp_hasDerivWithinAt r (hgd r hr)
    have h := (hre.mul hre).add (him.mul him)
    have e1 : f = fun s => (reCLM ∘ g) s * (reCLM ∘ g) s + (imCLM ∘ g) s * (imCLM ∘ g) s := by
      funext s; simp only [hf, normSq_apply, Function.comp_apply, reCLM_apply, imCLM_apply]
    have e2 : f' r = reCLM (g' r) * (reCLM ∘ g) r + (reCLM ∘ g) r * reCLM (g' r) +
        (imCLM (g' r) * (imCLM ∘ g) r + (imCLM ∘ g) r * imCLM (g' r)) := by
      simp only [hf', Function.comp_apply, reCLM_apply, imCLM_apply]; ring
    rw [e1, e2]; exact h
  set Bf : ℝ → ℝ := fun r => A ^ 2 * Real.exp (-(2 / 3) * (clk r - clk t₀)) with hBf
  set Bf' : ℝ → ℝ := fun r => Bf r * (-(2 / 3) * (Zr r ^ 2)⁻¹) with hBf'
  have hBd : ∀ r, HasDerivAt Bf (Bf' r) r := by
    intro r
    have h1 : HasDerivAt (fun r => -(2 / 3) * (clk r - clk t₀)) (-(2 / 3) * (Zr r ^ 2)⁻¹) r := by
      simpa using ((hclk r).sub_const (clk t₀)).const_mul (-(2 / 3 : ℝ))
    have h2 := h1.exp.const_mul (A ^ 2)
    exact h2.congr_deriv (by simp only [hBf', hBf]; ring)
  have hfence := image_le_of_deriv_right_lt_deriv_boundary' (f := f) (f' := f') (a := t₀) (b := t)
    (B := Bf) (B' := Bf')
    (fun r hr => (hfd r ⟨ht₀.trans hr.1, hr.2⟩).continuousWithinAt.mono (Icc_subset_Icc_left ht₀))
    (fun r hr => (hfd r ⟨ht₀.trans hr.1, hr.2.le⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hr.2) (Icc_subset_Icc_left (ht₀.trans hr.1))))
    (by
      simp only [hf, hBf, hg, sub_self, mul_zero, Real.exp_zero, mul_one]
      exact hA.le)
    (fun r _ => (hBd r).continuousAt.continuousWithinAt) (fun r _ => (hBd r).hasDerivWithinAt)
    (fun r hr hfB => by
      have hZ := hZpos r
      have hexp := Real.exp_pos (-(clk r - clk t₀) / 3)
      have hb := hbar r hr.1
      have hA2 : 0 < 2 * A * Real.exp (-(clk r - clk t₀) / 3) := by positivity
      have hBpos : 0 < Bf r := by positivity
      have hsq : Bf r < Zr r ^ 2 / 4 := by
        have h1 : (2 * A * Real.exp (-(clk r - clk t₀) / 3)) ^ 2 < Zr r ^ 2 := by
          exact pow_lt_pow_left₀ hb hA2.le (by norm_num)
        have h2 : (Real.exp (-(clk r - clk t₀) / 3)) ^ 2 = Real.exp (-(2 / 3) * (clk r - clk t₀)) := by
          rw [sq, ← Real.exp_add]; ring_nf
        have h3 : (2 * A * Real.exp (-(clk r - clk t₀) / 3)) ^ 2 = 4 * Bf r := by
          rw [mul_pow, h2, hBf]; ring
        linarith
      have hgle : normSq (g r) ≤ Zr r ^ 2 / 4 := by
        have : normSq (g r) = Bf r := hfB
        linarith
      have hin := inner_gap_le hZ hgle
      have hBeq : normSq (g r) = Bf r := hfB
      rw [hBeq] at hin
      have hv : g r + ((Zr r : ℝ) : ℂ) = v r := by simp only [hg]; ring
      have e : f' r = 2 * ((g r).re * (2 / (g r + ((Zr r : ℝ) : ℂ)) - 2 / ((Zr r : ℝ) : ℂ)).re +
          (g r).im * (2 / (g r + ((Zr r : ℝ) : ℂ)) - 2 / ((Zr r : ℝ) : ℂ)).im) := by
        rw [hv]
      have hB' : Bf' r = -(2 / 3) * Bf r / Zr r ^ 2 := by simp only [hBf']; field_simp
      have hZ2 : 0 < Zr r ^ 2 := by positivity
      rw [hB', e]
      have hlt : -(8 / 9) * Bf r / Zr r ^ 2 < -(2 / 3) * Bf r / Zr r ^ 2 :=
        div_lt_div_of_pos_right (by linarith) hZ2
      have h89 : -(8 / 9) * Bf r / Zr r ^ 2 = 2 * (-(4 / 9) * Bf r / Zr r ^ 2) := by ring
      linarith)
  exact fun r hr => hfence hr

/-! ### Points near the force point after `t₀` are never swallowed -/

/-- **No swallowing behind the fence**: if `z ∈ ℍ` is alive on `[0, t₀]` with `|f_r(z)| ≥ m₀` there and
`|f_{t₀}(z) − Z_{t₀}| < A`, and `2A e^{−(s_r − s_{t₀})/3} < Z_r` for all `r ≥ t₀`, then `z` is never swallowed. -/
theorem not_mem_fwdHull_of_barrier {W : ℝ → ℝ} (hW : Continuous W) {pR : ℝ} {Zr clk : ℝ → ℝ}
    (hZc : Continuous Zr) (hZpos : ∀ r, 0 < Zr r) (huR : ∀ T, IsForwardSol W pR T (fun s => ((Zr s : ℝ) : ℂ)))
    (hclk : ∀ r, HasDerivAt clk ((Zr r ^ 2)⁻¹) r) {z : ℂ} (hz : 0 < z.im) {t₀ m₀ A : ℝ} (ht₀ : 0 ≤ t₀)
    (hm₀ : 0 < m₀) {v : ℝ → ℂ} (hv : IsForwardSol W z t₀ v) (hvlow : ∀ r ∈ Icc 0 t₀, m₀ ≤ ‖v r‖)
    (hA : ‖v t₀ - Zr t₀‖ < A) (hbar : ∀ r, t₀ ≤ r → 2 * A * Real.exp (-(clk r - clk t₀) / 3) < Zr r)
    (T : ℝ) : z ∉ fwdHull W T := by
  intro hK
  obtain ⟨-, σ, hσT, hσ, hcl⟩ := (FwdClock.mem_fwdHull_iff_clock hW).1 hK
  have hA0 : 0 < A := lt_of_le_of_lt (norm_nonneg _) hA
  set T' := max T t₀ with hT'
  have hT'0 : 0 ≤ T' := le_max_of_le_right ht₀
  -- a lower bound for `Z` on `[0, T']`
  obtain ⟨r₁, hr₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT'0) hZc.continuousOn
  set mZ := Zr r₁ with hmZ
  have hmZ0 : 0 < mZ := hZpos r₁
  set μ := min m₀ (mZ / 2) with hμ
  have hμ0 : 0 < μ := lt_min hm₀ (half_pos hmZ0)
  obtain ⟨t, ht0, htσ, hM⟩ := hcl (T' / μ ^ 2)
  have htT : t ≤ T := htσ.le.trans hσT
  have hzt : z ∉ fwdHull W t := by
    rintro ⟨-, hle⟩
    rw [hσ, ENNReal.ofReal_le_ofReal_iff ht0] at hle
    linarith
  obtain ⟨v', hv'⟩ := exists_isForwardSol_of_not_mem_fwdHull ht0 hz hzt
  have hlow : ∀ r ∈ Icc (0 : ℝ) t, μ ≤ ‖fwdMap W r z‖ := by
    intro r hr
    rw [fwdMap_eq hW hz hv' hr]
    rcases le_total r t₀ with hrt | hrt
    · have hm : (0 : ℝ) ≤ min t t₀ := le_min ht0 ht₀
      have heq := eqOn_of_isForwardSol hW (isForwardSol_restrict hv' hm (min_le_left _ _))
        (isForwardSol_restrict hv hm (min_le_right _ _)) ⟨hr.1, le_min hr.2 hrt⟩
      rw [heq]
      exact (min_le_left _ _).trans (hvlow r ⟨hr.1, hrt⟩)
    · have htt₀ : t₀ ≤ t := hrt.trans hr.2
      have hv't₀ : v' t₀ = v t₀ :=
        eqOn_of_isForwardSol hW (isForwardSol_restrict hv' ht₀ htt₀) hv ⟨ht₀, le_rfl⟩
      have hAsq : normSq (v' t₀ - Zr t₀) < A ^ 2 := by
        rw [hv't₀, normSq_eq_norm_sq]
        exact pow_lt_pow_left₀ hA (norm_nonneg _) (by norm_num)
      have hfence := normSq_le_of_barrier hZpos (huR t) hclk hv' ht₀ hA0 hAsq hbar r ⟨hrt, hr.2⟩
      have hZr := hZpos r
      have hB : A ^ 2 * Real.exp (-(2 / 3) * (clk r - clk t₀)) < Zr r ^ 2 / 4 := by
        have hb := hbar r hrt
        have hA2 : 0 < 2 * A * Real.exp (-(clk r - clk t₀) / 3) := by positivity
        have h1 := pow_lt_pow_left₀ hb hA2.le (by norm_num : (2 : ℕ) ≠ 0)
        have h2 : (Real.exp (-(clk r - clk t₀) / 3)) ^ 2 = Real.exp (-(2 / 3) * (clk r - clk t₀)) := by
          rw [sq, ← Real.exp_add]; ring_nf
        rw [mul_pow, h2] at h1
        linarith
      have hlt : ‖v' r - Zr r‖ < Zr r / 2 := by
        have h1 : ‖v' r - Zr r‖ ^ 2 < (Zr r / 2) ^ 2 := by
          rw [← normSq_eq_norm_sq]; linarith
        exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
      have h2 := norm_sub_norm_le ((Zr r : ℝ) : ℂ) (v' r)
      rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZr] at h2
      have hr₁le : mZ ≤ Zr r := hmin ⟨hr.1, hr.2.trans (htT.trans (le_max_left _ _))⟩
      have : μ ≤ mZ / 2 := min_le_right _ _
      linarith
  have hclock : FwdClock.fwdClock W t z ≤ T' / μ ^ 2 := by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := 1 / μ ^ 2) (f := fun r => 1 / ‖fwdMap W r z‖ ^ 2) (fun r hr => by
        rw [uIoc_of_le ht0] at hr
        have h := hlow r ⟨hr.1.le, hr.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hμ0.le h 2))
    calc FwdClock.fwdClock W t z
        ≤ ‖∫ r in (0 : ℝ)..t, 1 / ‖fwdMap W r z‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 1 / μ ^ 2 * |t - 0| := hI
      _ ≤ T' / μ ^ 2 := by
        rw [sub_zero, abs_of_nonneg ht0, one_div_mul_eq_div]
        gcongr
        exact htT.trans (le_max_left _ _)
  linarith

/-! ### Real points at or beyond the force point -/

/-- A real point `x ≥ p_R` is alive on `[0, t₀]`, stays right of the force point, and contracts towards it. -/
theorem exists_realSol_right {W : ℝ → ℝ} (hW : Continuous W) {pR : ℝ} (hpR : W 0 < pR) {Zr : ℝ → ℝ}
    (hZpos : ∀ r, 0 < Zr r) (huR : ∀ T, IsForwardSol W pR T (fun s => ((Zr s : ℝ) : ℂ))) {x t₀ : ℝ}
    (hx : pR ≤ x) (ht₀ : 0 ≤ t₀) :
    ∃ ux : ℝ → ℂ, IsForwardSol W x t₀ ux ∧ (∀ r ∈ Icc 0 t₀, Zr r ≤ ‖ux r‖) ∧
      ‖ux t₀ - Zr t₀‖ ≤ x - pR := by
  rcases eq_or_lt_of_le hx with hxeq | hxlt
  · subst hxeq
    refine ⟨_, huR t₀, fun r _ => ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hZpos r)]
    · simp
  · obtain ⟨ux, hux⟩ := RS.exists_isForwardSol_of_lt hW ht₀ hpR hxlt (huR t₀)
    have hre : ∀ r ∈ Icc (0 : ℝ) t₀, Zr r < (ux r).re := fun r hr => by
      have := Zhan.re_lt_re_of_isForwardSol hW hxlt (huR t₀) hux hr
      simpa using this
    have him : ∀ r ∈ Icc (0 : ℝ) t₀, (ux r).im = 0 := fun r hr =>
      InteractingSLE.im_eq_zero_of_isForwardSol_real hW hux hr
    have hux_eq : ∀ r ∈ Icc (0 : ℝ) t₀, ux r = (((ux r).re : ℝ) : ℂ) := fun r hr =>
      Complex.ext (by simp) (by simp [him r hr])
    refine ⟨ux, hux, fun r hr => ?_, ?_⟩
    · rw [hux_eq r hr, Complex.norm_real, Real.norm_eq_abs]
      exact (hre r hr).le.trans (le_abs_self _)
    · have hc := re_sub_le_of_isForwardSol hW ht₀ (huR t₀) hux (fun r hr => by simpa using hre r hr)
        (fun r hr => by
          have h1 := hZpos r
          have h2 := hre r hr
          simp only [Complex.ofReal_re]
          nlinarith)
      have ht₀m : t₀ ∈ Icc (0 : ℝ) t₀ := ⟨ht₀, le_rfl⟩
      rw [hux_eq t₀ ht₀m, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [hre t₀ ht₀m])]
      simpa using hc

/-! ### Right clearance -/

/-- **Right clearance, deterministically** (added here). Let `w` be a continuous driver from `0` and `V^R` a right force
point from `p_R > 0` with `w < V^R` at all times. If for every `A ∈ ℕ` some `t₀` has
`2A e^{−(s_t − s_{t₀})/3} < V^R_t − w_t` for all `t ≥ t₀` (`s_t = ∫₀ᵗ (V^R − w)⁻²`), then for every `M` some `δ > 0`
keeps every hull point at distance `≥ δ` from `[p_R, M]`. -/
theorem exists_clearance_right {w vR : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hvR : Continuous vR)
    {pR : ℝ} (hpR : 0 < pR) (hlt : ∀ t, w t < vR t)
    (heq : ∀ t : ℝ≥0, vR t = pR + ∫ s in (0 : ℝ)..t, 2 / (vR s.toNNReal - w s.toNNReal))
    (hclear : ∀ A : ℕ, ∃ t₀ : ℝ≥0, ∀ t, t₀ ≤ t →
      2 * (A : ℝ) * Real.exp (-((∫ u in (0 : ℝ)..t, ((vR u.toNNReal - w u.toNNReal) ^ 2)⁻¹) -
        ∫ u in (0 : ℝ)..t₀, ((vR u.toNNReal - w u.toNNReal) ^ 2)⁻¹) / 3) < vR t - w t)
    (M : ℝ) :
    ∃ δ > (0 : ℝ), ∀ t : ℝ, ∀ z ∈ fwdHull (fun s : ℝ => w s.toNNReal) t, ∀ x ∈ Icc pR M, δ ≤ ‖z - x‖ := by
  set Wt : ℝ → ℝ := fun s => w s.toNNReal with hWt
  have hWc : Continuous Wt := hw.comp continuous_real_toNNReal
  set Zr : ℝ → ℝ := fun s => vR s.toNNReal - w s.toNNReal with hZr
  have hZc : Continuous Zr := (hvR.comp continuous_real_toNNReal).sub hWc
  have hZpos : ∀ r, 0 < Zr r := fun r => by simp only [hZr]; linarith [hlt r.toNNReal]
  have hgc : Continuous fun u => (Zr u ^ 2)⁻¹ := (hZc.pow 2).inv₀ fun u => pow_ne_zero 2 (hZpos u).ne'
  set clk : ℝ → ℝ := fun r => ∫ u in (0 : ℝ)..r, (Zr u ^ 2)⁻¹ with hclkdef
  have hclk : ∀ r, HasDerivAt clk ((Zr r ^ 2)⁻¹) r := fun r => (hgc.integral_hasStrictDerivAt 0 r).hasDerivAt
  have huR : ∀ T, IsForwardSol Wt pR T (fun s => ((Zr s : ℝ) : ℂ)) := fun T =>
    isForwardSol_of_force hw hvR (fun t => (hlt t).ne') heq T
  have hW0 : Wt 0 < pR := by simp only [hWt, Real.toNNReal_zero, hw0]; exact hpR
  obtain ⟨A, hA⟩ := exists_nat_gt (M - pR + 1)
  obtain ⟨t₀, ht₀⟩ := hclear A
  have hbar : ∀ r : ℝ, (t₀ : ℝ) ≤ r → 2 * (A : ℝ) * Real.exp (-(clk r - clk t₀) / 3) < Zr r := by
    intro r hr
    have hr0 : 0 ≤ r := t₀.coe_nonneg.trans hr
    have h := ht₀ r.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact hr)
    simp only [Real.coe_toNNReal _ hr0] at h
    exact h
  have ht₀0 : (0 : ℝ) ≤ t₀ := t₀.coe_nonneg
  obtain ⟨r₁, hr₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht₀0) hZc.continuousOn
  set m := Zr r₁ with hm
  have hm0 : 0 < m := hZpos r₁
  set δ' := m / 2 with hδ'
  have hδ'0 : 0 < δ' := half_pos hm0
  set E := Real.exp (2 / δ' ^ 2 * t₀) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set ε₀ := min (δ' / 2) (1 / 2) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min (by positivity) (by norm_num)
  refine ⟨ε₀ / (2 * E), by positivity, fun t z hz x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hzim : 0 < z.im := hz.1
  obtain ⟨ux, hux, hux_low, hux_c⟩ := exists_realSol_right hWc hW0 hZpos huR hx.1 ht₀0
  have hu_low : ∀ r ∈ Icc (0 : ℝ) t₀, 2 * δ' ≤ ‖ux r‖ := fun r hr => by
    have h3 : m ≤ Zr r := hmin hr
    have h2 := hux_low r hr
    simp only [hδ']; linarith
  have hzE : ‖z - x‖ * E < ε₀ / 2 := by
    have := mul_lt_mul_of_pos_right hcon hE0
    rwa [div_mul_eq_mul_div, mul_comm 2 E, ← div_div, mul_div_assoc, div_self hE0.ne', mul_one] at this
  have hzp : ‖z - x‖ * Real.exp (2 / δ' ^ 2 * t₀) < δ' := by
    have : ε₀ ≤ δ' / 2 := min_le_left _ _
    rw [← hE]; linarith
  have hzt₀ := not_mem_fwdHull_of_isForwardSol hWc hux hδ'0 hu_low hzim hzp
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_not_mem_fwdHull ht₀0 hzim hzt₀
  have hb := norm_sub_le_of_isForwardSol hWc hux hv hδ'0 ht₀0 le_rfl hu_low hzp
  have hbE : ∀ r ∈ Icc (0 : ℝ) t₀, ‖v r - ux r‖ < ε₀ / 2 := fun r hr => by
    refine lt_of_le_of_lt ((hb r hr).trans ?_) hzE
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hr.2 (by positivity))) (norm_nonneg _)
  have hvlow : ∀ r ∈ Icc (0 : ℝ) t₀, δ' ≤ ‖v r‖ := fun r hr => by
    have h1 := hu_low r hr
    have h2 := norm_sub_norm_le (ux r) (v r)
    rw [norm_sub_rev] at h2
    have h3 := hbE r hr
    have : ε₀ ≤ δ' / 2 := min_le_left _ _
    linarith
  have hAv : ‖v t₀ - Zr t₀‖ < A := by
    have h1 := hbE t₀ ⟨ht₀0, le_rfl⟩
    have h2 : ‖v t₀ - Zr t₀‖ ≤ ‖v t₀ - ux t₀‖ + ‖ux t₀ - Zr t₀‖ := by
      have := norm_add_le (v t₀ - ux t₀) (ux t₀ - Zr t₀)
      rwa [sub_add_sub_cancel] at this
    have : ε₀ ≤ 1 / 2 := min_le_right _ _
    linarith [hx.2]
  exact not_mem_fwdHull_of_barrier hWc hZc hZpos huR hclk hzim ht₀0 hδ'0 hv hvlow hAv hbar t hz

end InteractingSLE.ZhanGT4.A5Clear
