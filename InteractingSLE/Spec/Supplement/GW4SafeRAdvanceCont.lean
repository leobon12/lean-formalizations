/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanIdentify

/-!
# GW4: mean continuity from constancy of the positive-time phase

The explicit phase correction remains valid when the seeds coincide. This
includes time zero, where its harmonic measure is zero. Consequently a phase
constant only at positive times gives continuous phase-word means, for every
choice of bounded harmonic extension; its time-zero value needs no convention.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar Sec7 Sec7.PhaseSel

/-- The exact phase correction also holds for coincident seeds. -/
theorem couplingMean_eq_meanExt_add_phaseWindow {k : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {w : ℝ → ℝ} {t d : ℝ} {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    (hsep : vL 0 ≤ vR 0) {U : ℂ → ℝ}
    (hU : IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => vL i - w t) (fun j => vR j - w t) d)
      (forceJumpSet (fun i => vL i - w t) (fun j => vR j - w t)) U)
    {z : ℂ} (hf : fwdMap w t z ∈ H) :
    couplingMean k w t U z =
      couplingMean k w t (meanExt k ρL ρR (w t) vL vR) z +
        d * phaseWindow (vL 0 - w t) (vR 0 - w t) (fwdMap w t z) := by
  rcases hsep.lt_or_eq with hlt | heq
  · have h := couplingMean_sub_couplingMean_eq hlt hU hf
    linarith only [h]
  · have he : phaseData k ρL ρR (fun i => vL i - w t) (fun j => vR j - w t) d =
        forceBoundaryData k ρL ρR (fun i => vL i - w t) (fun j => vR j - w t) := by
      funext x
      simp only [phaseData, heq, Ioo_self, indicator_empty, mul_zero, add_zero]
    rw [he] at hU
    have hGG := Impl.eqOn_of_isBoundedHarmonicExtension
      (((Set.finite_range (fun i => vL i - w t)).union
        (Set.finite_range (fun j => vR j - w t))).insert 0)
      (isBoundedHarmonicExtension_meanExt k ρL ρR (w t) vL vR) hU
    simp only [phaseWindow, heq, sub_self, zero_div, mul_zero, add_zero]
    simp only [couplingMean, hGG hf]

/-- Canonical finite-word means are continuous on every protected interval. -/
theorem continuousOn_meanExt_couplingMean {k : ℝ} {nL nR : ℕ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {w : ℝ → ℝ} (hw : Continuous w)
    {vL : Fin nL → ℝ → ℝ} {vR : Fin nR → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hvL : ∀ i, ContinuousOn (vL i) (Icc 0 T))
    (hvR : ∀ j, ContinuousOn (vR j) (Icc 0 T))
    (hordL : ∀ q ∈ Icc 0 T, ∀ i, vL i q ≤ w q)
    (hordR : ∀ q ∈ Icc 0 T, ∀ j, w q ≤ vR j q)
    {z : ℂ} (hz : z ∈ H \ fwdHull w T) :
    ContinuousOn (fun r => couplingMean k w r
      (meanExt k ρL ρR (w r) (fun i => vL i r) (fun j => vR j r)) z) (Icc 0 T) := by
  have hv : ∀ j, ContinuousOn (fun r => jointV (fun i => vL i r) (fun j => vR j r) j)
      (Icc 0 T) := by
    intro j
    cases j with
    | inl i => exact hvL i
    | inr j => exact hvR j
  have hc := (continuousOn_const (c := Real.pi / Real.sqrt k * (1 + ∑ i, ρR i))).add
    (continuousOn_harmPart k (jointρ ρL ρR) hw hT hz hv)
  refine hc.congr fun r hr => ?_
  have hf := Ito.im_fwdMap_pos hw hT hz hr
  rw [couplingMean_meanExt_eq k ρL ρR (hordL r hr) (hordR r hr) hf]
  rfl

/-- Continuity of all phase-word means on a protected interval from continuous
coordinates and a phase constant at positive times. The phase at zero can be
arbitrary, since the two initial seeds coincide. -/
theorem continuousOn_couplingMean_of_positive_phase_const {k : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ}
    {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
    (hw : Continuous w) (hvL : ∀ i, Continuous (vL i)) (hvR : ∀ j, Continuous (vR j))
    (hordL : ∀ q i, vL i q ≤ w q) (hordR : ∀ q j, w q ≤ vR j q)
    (hseed : vL 0 0 = vR 0 0) {d : ℝ≥0 → ℝ} {c : ℝ} {U : ℝ≥0 → ℂ → ℝ}
    (hU : ∀ q, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => vL i q - w q) (fun j => vR j q - w q) (d q))
      (forceJumpSet (fun i => vL i q - w q) (fun j => vR j q - w q)) (U q))
    {T : ℝ} (hT : 0 ≤ T) (hd : ∀ q, 0 < q → q ≤ T.toNNReal → d q = c)
    {z : ℂ} (hz : z ∈ H \ fwdHull (fun r : ℝ => w r.toNNReal) T) :
    ContinuousOn (fun r : ℝ => couplingMean k (fun s : ℝ => w s.toNNReal)
      r (U r.toNNReal) z) (Icc 0 T) := by
  let wr : ℝ → ℝ := fun r => w r.toNNReal
  have hwc : Continuous wr := hw.comp continuous_real_toNNReal
  let X₀ : ℝ → ℝ := fun r => couplingMean k wr r
    (meanExt k ρL ρR (wr r) (fun i => vL i r.toNNReal) (fun j => vR j r.toNNReal)) z
  let pw : ℝ → ℝ := fun r => phaseWindow (vL 0 r.toNNReal - wr r)
    (vR 0 r.toNNReal - wr r) (fwdMap wr r z)
  have hX₀ : ContinuousOn X₀ (Icc 0 T) :=
    continuousOn_meanExt_couplingMean ρL ρR hwc hT
      (fun i => ((hvL i).comp continuous_real_toNNReal).continuousOn)
      (fun j => ((hvR j).comp continuous_real_toNNReal).continuousOn)
      (fun q _ => hordL q.toNNReal) (fun q _ => hordR q.toNNReal) hz
  have hpw : ContinuousOn pw (Icc 0 T) :=
    continuousOn_phaseWindow hwc hT hz
      ((((hvL 0).comp continuous_real_toNNReal).sub hwc).continuousOn)
      ((((hvR 0).comp continuous_real_toNNReal).sub hwc).continuousOn)
  refine (hX₀.add (hpw.const_mul c)).congr fun r hr => ?_
  have hf := Ito.im_fwdMap_pos hwc hT hz hr
  have he := couplingMean_eq_meanExt_add_phaseWindow (w := wr) (t := r)
    (vL := fun i => vL i r.toNNReal) (vR := fun j => vR j r.toNNReal)
    ((hordL r.toNNReal 0).trans (hordR r.toNNReal 0)) (hU r.toNNReal) hf
  change couplingMean k wr r (U r.toNNReal) z = X₀ r + c * pw r
  rw [he]
  change X₀ r + d r.toNNReal * pw r = X₀ r + c * pw r
  by_cases hr0 : r = 0
  · subst hr0
    simp only [pw, Real.toNNReal_zero, hseed, phaseWindow, sub_self, zero_div, mul_zero]
  · rw [hd r.toNNReal (Real.toNNReal_pos.2 (lt_of_le_of_ne hr.1 (Ne.symm hr0)))
      (Real.toNNReal_le_toNNReal hr.2)]

end InteractingSLE.Theorem14.GW4Fix
