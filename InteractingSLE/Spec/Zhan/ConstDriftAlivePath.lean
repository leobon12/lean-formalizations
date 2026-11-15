/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftAliveHit
import InteractingSLE.Spec.Zhan.ConstDriftHeight
import QuantumZipper.Proofs.RS.RealAlive

/-!
# From the strip lower gap to the chordal flow of a real point

Packet PROVE-ZHAN-A8. Let `(w, v)` be a separated mark pair on `[0, S]` (`Strip.IsSepMark`) with strip driver `ξ`
(`ξ_t = t + log(w − v)` at chordal time `s(t)`), and let `X` be a nonvanishing solution of the lower-gap equation
`X_t = q − ξ_t + ∫₀ᵗ C(X)` on `[0, T]`, `T ≥ t(S)`. With the strip point `P_t = q + ∫₀ᵗ C(X) = X_t + ξ_t`, the path

  `y_r = v_r + e^{P(t(r)) − t(r)} = v_r + (w_r − v_r) e^{X(t(r))}`

is `C¹` on `(0, S)` with `y' = 2/(v − w) + (y − v)(C(X) − 1)/(w − v)² = 2/(y − w)` (the `ξ`-terms cancel), and
`y_0 = e^q − 1`. Hence `u = y − w = (w − v)(e^{X(t(r))} − 1)` is a centred forward flow of the real point `e^q − 1`
on `[0, S]` (`isForwardSol_of_lowerGap`). No uniqueness is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol)

namespace InteractingSLE

namespace Zhan

namespace LowerGap

open Sec4 (cothHalf)
open Strip

theorem continuousOn_cothHalf_comp {X : ℝ → ℝ} {s : Set ℝ} (hXc : ContinuousOn X s) (hX0 : ∀ t ∈ s, X t ≠ 0) :
    ContinuousOn (fun t => cothHalf (X t)) s := by
  unfold cothHalf
  exact ((Real.continuous_exp.comp_continuousOn hXc).add continuousOn_const).div
    ((Real.continuous_exp.comp_continuousOn hXc).sub continuousOn_const) fun t ht => exp_sub_one_ne (hX0 t ht)

variable {w v : ℝ → ℝ} {S : ℝ}

/-- **From the strip lower gap to the chordal flow.** -/
theorem isForwardSol_of_lowerGap (h : IsSepMark w v S) {ξ : ℝ → ℝ}
    (hξ : ∀ t ∈ Icc 0 (stripClock w v S), stripDriver w v t = ξ t) {q T : ℝ} (hT : stripClock w v S ≤ T)
    {X : ℝ → ℝ} (hXc : ContinuousOn X (Icc 0 T)) (hX0 : ∀ t ∈ Icc 0 T, X t ≠ 0)
    (hX : ∀ t ∈ Icc 0 T, X t = q - ξ t + ∫ r in (0 : ℝ)..t, cothHalf (X r)) :
    IsForwardSol w ((Real.exp q - 1 : ℝ) : ℂ) S
      (fun r => (((w r - v r) * (Real.exp (X (stripClock w v r)) - 1) : ℝ) : ℂ)) := by
  set tc := stripClock w v with htc
  have hmono := h.strictMonoOn_stripClock
  have hSmem : S ∈ Icc 0 S := ⟨h.nonneg, le_rfl⟩
  have htcmem : ∀ r ∈ Icc 0 S, tc r ∈ Icc 0 T := fun r hr =>
    ⟨h.stripClock_nonneg hr, (hmono.monotoneOn hr hSmem hr.2).trans hT⟩
  have htcmem' : ∀ r ∈ Icc 0 S, tc r ∈ Icc 0 (tc S) := fun r hr =>
    ⟨h.stripClock_nonneg hr, hmono.monotoneOn hr hSmem hr.2⟩
  have htcc : ContinuousOn tc (Icc 0 S) := h.continuousOn_stripClock
  have hcoth : ContinuousOn (fun r => cothHalf (X r)) (Icc 0 T) := continuousOn_cothHalf_comp hXc hX0
  have hT0 : 0 ≤ T := (h.stripClock_nonneg hSmem).trans hT
  set P : ℝ → ℝ := fun t => q + ∫ r in (0 : ℝ)..t, cothHalf (X r) with hP
  have hPX : ∀ t ∈ Icc 0 T, P t = X t + ξ t := fun t ht => by rw [hP, hX t ht]; ring
  have hPc : ContinuousOn P (Icc 0 T) := by
    have hI := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (f := fun r => cothHalf (X r)) (by rw [uIcc_of_le hT0]; exact hcoth.integrableOn_Icc)
    rw [uIcc_of_le hT0] at hI
    exact continuousOn_const.add hI
  have hPd : ∀ t ∈ Ioo 0 T, HasDerivAt P (cothHalf (X t)) t := by
    intro t ht
    have hc' : ContinuousOn (fun r => cothHalf (X r)) (Ioo 0 T) := hcoth.mono Ioo_subset_Icc_self
    have hI := intervalIntegral.integral_hasDerivAt_right
      ((hcoth.mono (uIcc_subset_Icc ⟨le_rfl, hT0⟩ ⟨ht.1.le, ht.2.le⟩)).intervalIntegrable)
      (hc'.stronglyMeasurableAtFilter isOpen_Ioo t ht) (hc'.continuousAt (isOpen_Ioo.mem_nhds ht))
    exact hI.const_add q
  have hwv : ∀ r ∈ Icc 0 S, w r - v r = Real.exp (ξ (tc r) - tc r) := by
    intro r hr
    have h1 := hξ (tc r) (htcmem' r hr)
    rw [stripDriver, h.chordalTime_stripClock hr] at h1
    rw [← h1, add_sub_cancel_left, Real.exp_log (sub_pos.2 (h.lt r hr))]
  set y : ℝ → ℝ := fun r => v r + Real.exp (P (tc r) - tc r) with hy
  have hexp : ∀ r ∈ Icc 0 S, Real.exp (P (tc r) - tc r) = Real.exp (X (tc r)) * (w r - v r) := by
    intro r hr
    rw [hwv r hr, hPX _ (htcmem r hr), ← Real.exp_add]
    ring_nf
  have hyu : ∀ r ∈ Icc 0 S, y r - w r = (w r - v r) * (Real.exp (X (tc r)) - 1) := by
    intro r hr
    simp only [hy, hexp r hr]
    ring
  have hy0 : y 0 = Real.exp q - 1 := by
    simp only [hy, htc, IsSepMark.stripClock_zero, h.v_zero, hP, intervalIntegral.integral_same, add_zero,
      sub_zero]
    ring
  have hyc : ContinuousOn y (Icc 0 S) := by
    refine h.continuousOn_v.add (Real.continuous_exp.comp_continuousOn ((hPc.comp htcc htcmem).sub htcc))
  have hune : ∀ r ∈ Icc 0 S, (w r - v r) * (Real.exp (X (tc r)) - 1) ≠ 0 := fun r hr =>
    mul_ne_zero (sub_pos.2 (h.lt r hr)).ne' (exp_sub_one_ne (hX0 _ (htcmem r hr)))
  have hyd : ∀ r ∈ Ioo 0 S, HasDerivAt y (2 / (y r - w r)) r := by
    intro r hr
    have hrI : r ∈ Icc 0 S := Ioo_subset_Icc_self hr
    have htr : tc r ∈ Ioo 0 T := by
      refine ⟨?_, ?_⟩
      · have := hmono ⟨le_rfl, h.nonneg⟩ hrI hr.1
        rwa [IsSepMark.stripClock_zero] at this
      · exact (hmono hrI hSmem hr.2).trans_le hT
    have hv := h.hasDerivAt_v hr
    have htcd := h.hasDerivAt_stripClock hr
    have hPtc := (hPd (tc r) htr).comp r htcd
    have he := (hPtc.sub htcd).exp
    refine (hv.add he).congr_deriv ?_
    have ha : 0 < w r - v r := sub_pos.2 (h.lt r hrI)
    have hE := exp_sub_one_ne (hX0 _ (htcmem r hrI))
    rw [show (P ∘ tc - stripClock w v) r = P (tc r) - tc r from rfl, hyu r hrI, hexp r hrI, cothHalf]
    have hvw : v r - w r = -(w r - v r) := by ring
    rw [hvw]
    field_simp
    ring
  have hfc : ContinuousOn (fun r => 2 / (y r - w r)) (Icc 0 S) :=
    continuousOn_const.div (hyc.sub h.continuousOn_w) fun r hr => by rw [hyu r hr]; exact hune r hr
  have hFTC : ∀ r ∈ Icc 0 S, ∫ s in (0 : ℝ)..r, 2 / (y s - w s) = y r - y 0 := fun r hr =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 (hyc.mono (Icc_subset_Icc_right hr.2))
      (fun x hx => hyd x ⟨hx.1, hx.2.trans_le hr.2⟩)
      ((hfc.mono (uIcc_subset_Icc ⟨le_rfl, h.nonneg⟩ hr)).intervalIntegrable)
  refine ⟨Complex.continuous_ofReal.comp_continuousOn ((h.continuousOn_w.sub h.continuousOn_v).mul
    ((Real.continuous_exp.comp_continuousOn (hXc.comp htcc htcmem)).sub continuousOn_const)),
    fun r hr => ⟨by simp only [ne_eq, Complex.ofReal_eq_zero]; exact hune r hr, ?_⟩⟩
  have hcongr : ∫ s in (0 : ℝ)..r, (2 : ℂ) / ((((w s - v s) * (Real.exp (X (tc s)) - 1) : ℝ)) : ℂ) =
      ((∫ s in (0 : ℝ)..r, 2 / (y s - w s) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hr.1] at hs
    rw [hyu s ⟨hs.1, hs.2.trans hr.2⟩]
    push_cast
    rfl
  show ((((w r - v r) * (Real.exp (X (tc r)) - 1) : ℝ)) : ℂ) = _
  rw [hcongr, hFTC r hr, hy0, ← hyu r hr]
  push_cast
  ring

/-- **The strip-path form.** On the strip life, a nonvanishing lower-gap solution `X` with `X_0 = q` on `[0, T]`,
`T ≥ t(s)`, gives a centred forward flow of the chordal point `e^q − 1` on `[0, s]`. -/
theorem exists_isForwardSol_of_lowerGap {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ξ : ℝ≥0 → ℝ}
    (hd : HasStripDriver w v ζ ξ) {s : ℝ≥0} (hs : IsStripLife w v ζ s) {q T : ℝ}
    (hT : stripClock (extPath w) (extPath v) s ≤ T) {X : ℝ → ℝ} (hXc : ContinuousOn X (Icc 0 T))
    (hX0 : ∀ t ∈ Icc 0 T, X t ≠ 0)
    (hX : ∀ t ∈ Icc 0 T, X t = q - ξ t.toNNReal + ∫ r in (0 : ℝ)..t, cothHalf (X r)) :
    ∃ u : ℝ → ℂ, IsForwardSol (extPath w) ((Real.exp q - 1 : ℝ) : ℂ) s u := by
  have hsep := hd.1.2.1 s hs
  refine ⟨_, isForwardSol_of_lowerGap hsep (ξ := fun t => ξ t.toNNReal) (fun t ht => ?_) hT hXc hX0 hX⟩
  have h1 := hd.2 t.toNNReal
  rwa [Real.coe_toNNReal t ht.1] at h1

end LowerGap

end Zhan

end InteractingSLE
