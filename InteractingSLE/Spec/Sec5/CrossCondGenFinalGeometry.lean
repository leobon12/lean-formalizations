/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenFinalChain

/-!
# The precontact relative chain directly from two generating traces

PROVE-CROSSCOND-GEN. The counterflow is frozen using the generic nonsimple-trace
extension from `CrossRestartKernelCfSide`. Physical precontact separation supplies
the closed-hull separation by GB6, even when the original curves touch the real line.
Thus the pathwise relative driver has no remaining fixed-hull restriction input.
This does not yet give its stochastic force-coordinate transport or marked kernels.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito Supp8.GB6

/-- The relative filled-hull chain before the first physical contact, read in the
original counterflow chart. Both source drivers may have finite available lifetime.
No simplicity or exclusion of original-real contacts is assumed. -/
theorem exists_relativeImage_of_traces
    {w wc : ℝ≥0 → ℝ} {ζ ζc Tc : ℝ≥0∞} {α γ : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace w ζ α) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hγ : IsGeneratingTrace wc ζc γ) (hwc : ContinuousOn wc {t | (t : ℝ≥0∞) < ζc}) (hwc0 : wc 0 = 0)
    {s : ℝ≥0} (hs : 0 < s) (hsζ : (s : ℝ≥0∞) < ζc)
    (hTc : 0 < Tc) (hTcζ : Tc ≤ ζ)
    (hcontact : Tc ≤ firstContactTime (fun t => sphereInv (α t : OnePoint ℂ))
      ((fun t => (γ t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ W' : ℝ≥0 → ℝ, W' 0 = 0 ∧ relClock (rpath wc) s (rpath w) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock (rpath wc) s (rpath w) t) {t | (t : ℝ≥0∞) < Tc} ∧
      ContinuousOn (fun t : ℝ≥0 => relClock (rpath wc) s (rpath w) t) {t | (t : ℝ≥0∞) < Tc} ∧
      ContinuousOn W' {u | ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ (u : ℝ) < relClock (rpath wc) s (rpath w) t} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
        QuantumZipper.fwdHull (rpath W') (relClock (rpath wc) s (rpath w) t) =
          relMap (rpath wc) s '' QuantumZipper.fwdHull (rpath w) t ∧
        IsFilling (QuantumZipper.fwdHull (rpath W') (relClock (rpath wc) s (rpath w) t))
          (relMap (rpath wc) s '' (α '' Icc 0 t ∩ H)) := by
  obtain ⟨U, β, hU, hU0, hβ, heU, heβ, heK⟩ :=
    CrossRestart.exists_frozen_isLoewnerTrace hγ hwc hwc0 hsζ
  have he : ∀ r ∈ Icc (0 : ℝ) s, U r = rpath wc r := heU
  have htip := hβ.tendsto_fwdMapInv_tip hU hU0 s.coe_nonneg
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc →
      Disjoint (closure (QuantumZipper.fwdHull U s))
        (closure ((fun z : ℂ => -z⁻¹) '' QuantumZipper.fwdHull (rpath w) T)) := by
    intro T hT
    rw [heK s ⟨s.coe_nonneg, le_rfl⟩]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hγ hwc hwc0 hα hw hw0 hsζ
      (hT.trans_le hTcζ) (hT.trans_le hcontact)
  obtain ⟨V, hV⟩ := exists_relativeImage_before_lifetime hw hw0 hU hU0 (by exact_mod_cast hs)
    htip hTc hTcζ hα hd
  have hM := relMap_eq_of_eqOn s.coe_nonneg he
  have hA := relClock_eq_of_eqOn s.coe_nonneg he (fun r : ℝ => w r.toNNReal)
  refine ⟨V, ?_⟩
  rw [hA, hM] at hV
  exact hV

end InteractingSLE.Sec5.CrossCond.Gen
