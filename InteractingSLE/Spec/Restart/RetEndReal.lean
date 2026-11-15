/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetEndLimit
import InteractingSLE.Spec.Restart.RetLeafEndReal
import InteractingSLE.Foundations.Loewner.FiniteEndpointStatement
import InteractingSLE.Spec.Sec2.TerminalEscape

/-!
# A generated integrated SLE path ends on the real line at a finite lifetime

Packet PROVE-T15-RET2. Proof of PROVE-T15-RET's named deterministic input
`RetLeaf.IntegratedPathEndRealStatement` (`integratedPathEndRealStatement`), and hence the three trace facts of
the retained continuation without any named input (`retained_traceInputs_of_flowLine`).

## Proof

Let `ζ = T` be finite. At `T = 0` the trace is at its seed `0`. Let `T > 0`.

1. **Driver limit.** The trace is continuous through `T`, so the driver has a finite limit `c` as
   `t ↑ T` (`exists_tendsto_driver_of_isGeneratingTrace`, `RetEndLimit.lean`: [Yua22] Theorem 1.1
   (ii) ⇒ (i) on the closed interval).
2. **Force limits.** The driver is bounded on `[0, T)` (it extends continuously to `[0, T]`,
   `FiniteEndpoint.continuous_extDriver`), so the right force points are bounded above and the left ones
   below (`IsForcePath.vR_le_of_w_le`, `vL_ge_of_le_w`); being monotone (`monotoneOn_vR`,
   `antitoneOn_vL`), they converge.
3. **Threshold.** The state converges, so by maximality of the lifetime (the frozen
   `IsIntegratedSLEPath`'s last conjunct) the limit is a threshold state.
4. **The tip is real.** `IsForcePath.notMem_H_of_isGeneratingTrace` (a colliding force image forces the
   tip out of `ℍ`) gives `η(T) ∉ ℍ`, and the trace lies in `ℍ̄` (`Sec7.IsGeneratingTrace.mem_Hbar`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE.Restart.RetEnd

/-- **A generated integrated SLE path ends on the real line at a finite lifetime** (deterministic): the
named input of PROVE-T15-RET is proved. -/
theorem integratedPathEndRealStatement : RetLeaf.IntegratedPathEndRealStatement := by
  intro a nL nR xL xR ρL ρR w vL vR b ζ η hp hg hζ
  obtain ⟨T, rfl⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ := ⟨ζ.toNNReal, ENNReal.coe_toNNReal hζ⟩
  rw [ENNReal.toNNReal_coe]
  have hw : ContinuousOn w {t | (t : ℝ≥0∞) < (T : ℝ≥0∞)} := hp.2.2.2.1
  have hw0 : w 0 = 0 := hp.1
  rcases (zero_le (a := T)).lt_or_eq with hT | hT
  swap
  · rw [← hT, hg.1, Complex.zero_im]
  -- 1. the driver converges
  obtain ⟨c, hc⟩ := exists_tendsto_driver_of_isGeneratingTrace hg hw hw0 hT
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < (T : ℝ≥0∞)} = Iio T := Sec2.setOf_lt_coe_eq_Iio T
  -- 2. the driver is bounded before `T`, hence so are the force points
  have hE := FiniteEndpoint.continuous_extDriver (hset ▸ hw) hc
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hE.continuousOn
  have hbd : ∀ s : ℝ≥0, (s : ℝ≥0∞) < (T : ℝ≥0∞) → |w s| ≤ M := by
    intro s hs
    have hsT : (s : ℝ) < T := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hs)
    have h := hM s ⟨s.coe_nonneg, hsT.le⟩
    rwa [FiniteEndpoint.extDriver_of_lt s.coe_nonneg hsT, Real.toNNReal_coe,
      Real.norm_eq_abs] at h
  have hfp := hp.isForcePath
  have hRb : ∀ j, ∃ M' : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M' := fun j =>
    ⟨max (xR j) (M + 1) + 2 * T, fun s hs => by
      have h1 := hfp.vR_le_of_w_le (m := M) (fun r hr => (abs_le.1 (hbd r hr)).2) j
        (ENNReal.coe_lt_coe.2 hs)
      have h2 : (s : ℝ) ≤ T := NNReal.coe_le_coe.2 hs.le
      linarith⟩
  have hLb : ∀ i, ∃ M' : ℝ, ∀ s : ℝ≥0, s < T → M' ≤ vL i s := fun i =>
    ⟨min (xL i) (-M - 1) - 2 * T, fun s hs => by
      have h1 := hfp.vL_ge_of_le_w (m := -M) (fun r hr => (abs_le.1 (hbd r hr)).1) i
        (ENNReal.coe_lt_coe.2 hs)
      have h2 : (s : ℝ) ≤ T := NNReal.coe_le_coe.2 hs.le
      linarith⟩
  have hL : ∀ i, Tendsto (vL i) (𝓝[<] T) (𝓝 (sInf (vL i '' Iio T))) := fun i => by
    refine AntitoneOn.tendsto_nhdsLT ?_ ?_
    · have h := hfp.antitoneOn_vL i
      rwa [hset] at h
    · obtain ⟨M', hM'⟩ := hLb i
      exact ⟨M', by rintro _ ⟨s, hs, rfl⟩; exact hM' s hs⟩
  have hR : ∀ j, Tendsto (vR j) (𝓝[<] T) (𝓝 (sSup (vR j '' Iio T))) := fun j => by
    refine MonotoneOn.tendsto_nhdsLT ?_ ?_
    · have h := hfp.monotoneOn_vR j
      rwa [hset] at h
    · obtain ⟨M', hM'⟩ := hRb j
      exact ⟨M', by rintro _ ⟨s, hs, rfl⟩; exact hM' s hs⟩
  -- 3. the state converges to a threshold state
  have hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (c, fun i => sInf (vL i '' Iio T), fun j => sSup (vR j '' Iio T))) :=
    hc.prodMk_nhds ((tendsto_pi_nhds.2 hL).prodMk_nhds (tendsto_pi_nhds.2 hR))
  have hthr := hfp.threshold_of_tendsto hT rfl hlim
  -- 4. the tip is real
  have hnot := hfp.notMem_H_of_isGeneratingTrace hg hT rfl hlim hthr
  have hHbar : η T ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hg hw hw0 le_rfl
  exact le_antisymm (not_lt.1 hnot) hHbar

/-- A flow line ends on the real line at a finite lifetime (no named input). -/
theorem ae_flowLine_end_real {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ζ ω ≠ ⊤ → (η ω (ζ ω).toNNReal).im = 0 :=
  RetLeaf.ae_flowLine_end_real integratedPathEndRealStatement hη

section Retained

open Supp7 RetAux79 Sec7

variable {Ω : Type*} [MeasurableSpace Ω] {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {x₁ x₂ : ℝ}

/-- **The three trace facts of the retained continuation, unconditionally**: `RetLeaf.retained_traceInputs`
with its named input discharged by `integratedPathEndRealStatement`. -/
theorem retained_traceInputs_of_flowLine {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {θ₂ : ℝ} {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η₂ : Ω → ℝ≥0 → ℂ} (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) {F : Set Ω}
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁) (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂) :
    (∀ᵐ ω ∂P, ω ∈ F → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω →
      0 < (RetAux79.retPath G η₁' η₂' ζ₂ u r ω t).im) ∧
    (∀ᵐ ω ∂P, ω ∈ F → F.indicator (retLife G η₁' η₂' ζ₂ u r) ω ≠ ⊤ →
      (RetAux79.retPath G η₁' η₂' ζ₂ u r ω
        (F.indicator (retLife G η₁' η₂' ζ₂ u r) ω).toNNReal).im = 0) ∧
    (∀ᵐ ω ∂P, ω ∈ F → 0 < F.indicator (retLife G η₁' η₂' ζ₂ u r) ω) :=
  RetLeaf.retained_traceInputs integratedPathEndRealStatement hη₂ ha₂ hd hF hp₁ hp₂

end Retained

end InteractingSLE.Restart.RetEnd
