/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftCluster
import InteractingSLE.Spec.Zhan.UpperPoint

/-!
# Constant strip drift `|σ| < 1`: the upper gap of a chordal point left of the end mark

Packet PROVE-ZHAN-A5. Astra, *Formalization proofs and dependency audit* (ruling R35), "Unique upper accumulation
point" (`source/external/AstraIG1/ig1_formalization_proofs.txt` L1441–L1447) and "Complete upper-point diffusion
calculation" (L1170–L1219). For a strip path and a chordal point `y < −1` (the upper point `x + iπ`,
`x = log(−1 − y)`), with its flow `u_y` under the frozen driver, the **upper gap**

  `X_t = Re ψ_t(x + iπ) − ξ_t = p_t − ξ_t`,  `p_t = t + log |y_{s(t)} − v_{s(t)}|`   (`upperGapOf`)

solves the ODE `X_t = x − ξ_t + ∫₀ᵗ tanh(X_u/2) du` (3.15) on `[0, t(s')]` (PROVE-ZHAN-A's `IsSepMark.upperGap_eq`),
and the two chordal integrals of `ConstDriftCluster.lean` are its exponential moments in strip time:

  `∫₀^{s'} 2/((v − y)(w − v)) ds = ∫₀^{t(s')} 2e^{−X}`,   `∫₀^{s'} 2(v − y)/(w − v)³ ds = ∫₀^{t(s')} 2e^{X}`

(substitution `u = t(s)`, `dt = ds/(w − v)²`, `e^{X} = (v − y)/(w − v)`).

## Main results

* `IsStripPath.upperGapOf_ode`, `IsStripPath.continuousOn_upperGapOf`;
* `IsStripPath.integral_left_eq_upperGap`, `IsStripPath.integral_right_eq_upperGap`;
* `IsStripPath.integral_sech_eq_upperGap`: `∫₀^{s'} (2/(u_y(v − w)) − 2/u_y²) = ∫₀^{t(s')} 1/(1 + cosh X)`
  (`= ½∫ sech²(X/2)`, the exponent of (3.23)).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace Zhan

open Strip

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The upper gap `X_t = p_t − ξ_t` of the chordal point whose centred flow is `uy`. -/
def upperGapOf (w v : ℝ≥0 → ℝ) (uy : ℝ → ℂ) (t : ℝ) : ℝ :=
  stripPoint (extPath w) (extPath v) (fun r => (uy r).re + extPath w r) t -
    stripDriver (extPath w) (extPath v) t

section Data

variable {y : ℝ} {s' s'' : ℝ≥0} {uy : ℝ → ℂ}

/-- The chordal point path `y_r = u_y(r) + w_r` satisfies the hypotheses of `IsSepMark.upperGap_eq`. -/
theorem IsStripPath.upper_path_props (h : IsStripPath w v ζ) (hy : y < -1) (hs's'' : s' < s'')
    (hs'' : IsStripLife w v ζ s'') (huy : IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy) :
    IsSepMark (extPath w) (extPath v) s' ∧
      ContinuousOn (fun r => (uy r).re + extPath w r) (Icc 0 s') ∧
      IntervalIntegrable (fun u => 2 / ((uy u).re + extPath w u - extPath w u)) volume 0 s' ∧
      (∀ r ∈ Icc (0 : ℝ) s', (uy r).re + extPath w r =
        ((uy 0).re + extPath w 0) + ∫ u in (0 : ℝ)..r, 2 / ((uy u).re + extPath w u - extPath w u)) ∧
      (∀ r ∈ Icc (0 : ℝ) s', (uy r).re + extPath w r < extPath v r) ∧
      (uy 0).re + extPath w 0 = y := by
  have hs' : IsStripLife w v ζ s' := hs''.mono hs's''.le
  have hm := h.2.1 s' hs'
  have hw0 : w 0 = 0 := h.1
  have hfc : Continuous (frozenDrive w s'') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.continuousOn_le hs'')
  have huV := h.isForwardSol_end hs'' hs's''.le
  have hfz : ∀ r ∈ Icc (0 : ℝ) s', frozenDrive w s'' r = extPath w r := fun r hr => by
    rw [frozenDrive_eq ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.2 hs's''.le)⟩]; rfl
  have hc := continuousOn_re_of_isForwardSol huy
  have hn := fun r (hr : r ∈ Icc (0 : ℝ) s') => re_ne_zero_of_isForwardSol_real hfc huy hr
  have hsimp : ∀ u, (uy u).re + extPath w u - extPath w u = (uy u).re := fun u => by ring
  refine ⟨hm, hc.add hm.continuousOn_w, ?_, fun r hr => ?_, fun r hr => ?_, ?_⟩
  · simp only [hsimp]
    exact (continuousOn_const.div hc hn).intervalIntegrable_of_Icc (NNReal.coe_nonneg s')
  · simp only [hsimp]
    have h1 := re_eq_of_isForwardSol_real hfc huy hr
    have h0 := re_eq_of_isForwardSol_real hfc huy ⟨le_rfl, NNReal.coe_nonneg s'⟩
    rw [hfz r hr] at h1
    rw [hfz 0 ⟨le_rfl, NNReal.coe_nonneg s'⟩] at h0
    simp only [intervalIntegral.integral_same, add_zero] at h0
    rw [h1, h0]
    ring
  · have h1 := flow_re_lt_flow_re hfc huy huV hy hr
    simp only [ofReal_re] at h1
    linarith
  · have h0 := re_eq_of_isForwardSol_real hfc huy ⟨le_rfl, NNReal.coe_nonneg s'⟩
    rw [hfz 0 ⟨le_rfl, NNReal.coe_nonneg s'⟩] at h0
    simp only [intervalIntegral.integral_same, add_zero] at h0
    rw [h0]
    ring

/-- **(3.15) for the upper gap**: `X_t = log(−1 − y) − ξ_t + ∫₀ᵗ tanh(X_u/2) du` on `[0, t(s')]`. -/
theorem IsStripPath.upperGapOf_ode (h : IsStripPath w v ζ) (hy : y < -1) (hs's'' : s' < s'')
    (hs'' : IsStripLife w v ζ s'') (huy : IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy) {t : ℝ}
    (ht : t ∈ Icc 0 (stripClock (extPath w) (extPath v) s')) :
    upperGapOf w v uy t = Real.log (-1 - y) - stripDriver (extPath w) (extPath v) t +
      ∫ u in (0 : ℝ)..t, Real.tanh (upperGapOf w v uy u / 2) := by
  obtain ⟨hm, hyc, hint, heq, hyv, hy0⟩ := h.upper_path_props hy hs's'' hs'' huy
  have key := hm.upperGap_eq hyc hint heq hyv ht
  have hX0 : stripPoint (extPath w) (extPath v) (fun r => (uy r).re + extPath w r) 0 =
      Real.log (-1 - y) := by
    simp only [stripPoint, hm.chordalTime_zero, zero_add, hm.v_zero]
    rw [hy0, show y - -1 = -(-1 - y) by ring, abs_neg, abs_of_pos (by linarith)]
  have hξ0 : stripDriver (extPath w) (extPath v) 0 = 0 :=
    hm.stripDriver_zero (by simp [extPath, h.1])
  unfold upperGapOf
  rw [hX0, hξ0] at key
  linarith

theorem IsStripPath.continuousOn_upperGapOf (h : IsStripPath w v ζ) (hy : y < -1) (hs's'' : s' < s'')
    (hs'' : IsStripLife w v ζ s'') (huy : IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy) :
    ContinuousOn (upperGapOf w v uy) (Icc 0 (stripClock (extPath w) (extPath v) s')) := by
  obtain ⟨hm, hyc, -, -, hyv, -⟩ := h.upper_path_props hy hs's'' hs'' huy
  exact (hm.continuousOn_stripPoint hyc fun r hr => (hyv r hr).ne).sub hm.continuousOn_stripDriver

/-- At the strip time `t(r)`, `X = log((v − y)/(w − v))`. -/
theorem IsStripPath.upperGapOf_stripClock (h : IsStripPath w v ζ) (hy : y < -1) (hs's'' : s' < s'')
    (hs'' : IsStripLife w v ζ s'') (huy : IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) s') :
    upperGapOf w v uy (stripClock (extPath w) (extPath v) r) =
      Real.log ((extPath v r - extPath w r) - (uy r).re) - Real.log (extPath w r - extPath v r) := by
  obtain ⟨hm, -, -, -, hyv, -⟩ := h.upper_path_props hy hs's'' hs'' huy
  simp only [upperGapOf, stripPoint, stripDriver, hm.chordalTime_stripClock hr]
  rw [abs_sub_comm, abs_of_pos (sub_pos.2 (hyv r hr))]
  ring_nf

/-- The substitution `u = t(r)` for a function of the strip time. -/
theorem IsStripPath.integral_comp_stripClock (h : IsStripPath w v ζ) (hs' : IsStripLife w v ζ s')
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 (stripClock (extPath w) (extPath v) s'))) :
    ∫ r in (0 : ℝ)..s', g (stripClock (extPath w) (extPath v) r) *
        ((extPath w r - extPath v r) ^ 2)⁻¹ =
      ∫ u in (0 : ℝ)..(stripClock (extPath w) (extPath v) s'), g u := by
  have hm := h.2.1 s' hs'
  have hS := hm.nonneg
  have hcs := intervalIntegral.integral_comp_mul_deriv'' (a := 0) (b := (s' : ℝ))
    (f := stripClock (extPath w) (extPath v)) (f' := fun r => ((extPath w r - extPath v r) ^ 2)⁻¹) (g := g)
    (by rw [uIcc_of_le hS]; exact hm.continuousOn_stripClock)
    (fun x hx => by
      rw [min_eq_left hS, max_eq_right hS] at hx
      exact (hm.hasDerivAt_stripClock hx).hasDerivWithinAt)
    (by rw [uIcc_of_le hS]; exact hm.continuousOn_inv_sq)
    (by
      rw [uIcc_of_le hS]
      refine hg.mono ?_
      rintro _ ⟨r, hr, rfl⟩
      exact ⟨hm.stripClock_nonneg hr, hm.strictMonoOn_stripClock.monotoneOn hr ⟨hS, le_rfl⟩ hr.2⟩)
  rw [IsSepMark.stripClock_zero] at hcs
  rw [← hcs]
  rfl

/-- **The left chordal integral is `∫ 2e^{−X}` in strip time.** -/
theorem IsStripPath.integral_left_eq_upperGap (h : IsStripPath w v ζ) (hy : y < -1) (hs's'' : s' < s'')
    (hs'' : IsStripLife w v ζ s'') (huy : IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy) :
    ∫ r in (0 : ℝ)..s', 2 / (((extPath v r - extPath w r) - (uy r).re) * -(extPath v r - extPath w r)) =
      ∫ u in (0 : ℝ)..(stripClock (extPath w) (extPath v) s'), 2 * Real.exp (-upperGapOf w v uy u) := by
  have hs' : IsStripLife w v ζ s' := hs''.mono hs's''.le
  obtain ⟨hm, -, -, -, hyv, -⟩ := h.upper_path_props hy hs's'' hs'' huy
  rw [← h.integral_comp_stripClock hs' (g := fun u => 2 * Real.exp (-upperGapOf w v uy u))
    (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
      (h.continuousOn_upperGapOf hy hs's'' hs'' huy).neg))]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hm.nonneg] at hr
  rw [h.upperGapOf_stripClock hy hs's'' hs'' huy hr]
  have h1 : 0 < extPath w r - extPath v r := sub_pos.2 (hm.lt r hr)
  have h2 : 0 < (extPath v r - extPath w r) - (uy r).re := by linarith [hyv r hr]
  rw [show -(Real.log ((extPath v r - extPath w r) - (uy r).re) - Real.log (extPath w r - extPath v r)) =
    Real.log (extPath w r - extPath v r) - Real.log ((extPath v r - extPath w r) - (uy r).re) by ring]
  rw [Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
  have e : -(extPath v r - extPath w r) = extPath w r - extPath v r := by ring
  rw [e]
  field_simp

/-- **The right chordal integral is `∫ 2e^{X}` in strip time.** -/
theorem IsStripPath.integral_right_eq_upperGap (h : IsStripPath w v ζ) (hy : y < -1) (hs's'' : s' < s'')
    (hs'' : IsStripLife w v ζ s'') (huy : IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy) :
    ∫ r in (0 : ℝ)..s', 2 * ((extPath v r - extPath w r) - (uy r).re) / (-(extPath v r - extPath w r)) ^ 3 =
      ∫ u in (0 : ℝ)..(stripClock (extPath w) (extPath v) s'), 2 * Real.exp (upperGapOf w v uy u) := by
  have hs' : IsStripLife w v ζ s' := hs''.mono hs's''.le
  obtain ⟨hm, -, -, -, hyv, -⟩ := h.upper_path_props hy hs's'' hs'' huy
  rw [← h.integral_comp_stripClock hs' (g := fun u => 2 * Real.exp (upperGapOf w v uy u))
    (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
      (h.continuousOn_upperGapOf hy hs's'' hs'' huy)))]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hm.nonneg] at hr
  rw [h.upperGapOf_stripClock hy hs's'' hs'' huy hr]
  have h1 : 0 < extPath w r - extPath v r := sub_pos.2 (hm.lt r hr)
  have h2 : 0 < (extPath v r - extPath w r) - (uy r).re := by linarith [hyv r hr]
  rw [Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
  have e : -(extPath v r - extPath w r) = extPath w r - extPath v r := by ring
  rw [e]
  field_simp

/-- **The derivative integral is `½∫ sech²(X/2) = ∫ 1/(1 + cosh X)` in strip time** ((3.23)). -/
theorem IsStripPath.integral_sech_eq_upperGap (h : IsStripPath w v ζ) (hy : y < -1) (hs's'' : s' < s'')
    (hs'' : IsStripLife w v ζ s'') (huy : IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy) :
    ∫ r in (0 : ℝ)..s', (2 / ((uy r).re * (extPath v r - extPath w r)) - 2 / (uy r).re ^ 2) =
      ∫ u in (0 : ℝ)..(stripClock (extPath w) (extPath v) s'), 1 / (1 + Real.cosh (upperGapOf w v uy u)) := by
  have hs' : IsStripLife w v ζ s' := hs''.mono hs's''.le
  obtain ⟨hm, -, -, -, hyv, -⟩ := h.upper_path_props hy hs's'' hs'' huy
  rw [← h.integral_comp_stripClock hs' (g := fun u => 1 / (1 + Real.cosh (upperGapOf w v uy u)))
    (continuousOn_const.div (continuousOn_const.add (Real.continuous_cosh.comp_continuousOn
      (h.continuousOn_upperGapOf hy hs's'' hs'' huy))) fun u _ => by
        linarith [Real.one_le_cosh (upperGapOf w v uy u)])]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hm.nonneg] at hr
  rw [h.upperGapOf_stripClock hy hs's'' hs'' huy hr]
  set A := extPath w r - extPath v r with hA
  set B := (extPath v r - extPath w r) - (uy r).re with hB
  have h1 : 0 < A := sub_pos.2 (hm.lt r hr)
  have h2 : 0 < B := by rw [hB]; linarith [hyv r hr]
  have hu : (uy r).re = -A - B := by rw [hA, hB]; ring
  have hv : extPath v r - extPath w r = -A := by rw [hA]; ring
  have hc : 1 + Real.cosh (Real.log B - Real.log A) = (A + B) ^ 2 / (2 * A * B) := by
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
    field_simp
    ring
  have hAB : 0 < A + B := by linarith
  rw [hu, hv, hc]
  have e1 : (-A - B) * -A = (A + B) * A := by ring
  have e2 : (-A - B) ^ 2 = (A + B) ^ 2 := by ring
  rw [e1, e2]
  field_simp
  ring

end Data

end Zhan

end InteractingSLE
