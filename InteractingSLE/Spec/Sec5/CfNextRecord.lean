/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishRecord
import InteractingSLE.Spec.Sec5.StagedRepStrict

/-!
# Strict separation of the actual positive-time record marks

Packet PROVE-CFCHART2. Reuse the strict chart-image lemmas and the survival of
nonzero real points for a trace contained in the upper half-plane.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfNext

open CfConv CfChart Exist Exist.Staged Exist.StagedLaw Restart LawUnique Prop411Q
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47 CrossCond.Word49
open WangWu (seedLine)

/-- Good flow records strictly separate every original strictly ordered side list
and its appended junction. The real-survival input follows from the existing trace. -/
theorem record_strict_of_good {Z : Type*} {nL nR mL mR : ℕ}
    {W : ℝ≥0 → Z → ℝ} {VL : Fin nL → ℝ≥0 → Z → ℝ}
    {VR : Fin nR → ℝ≥0 → Z → ℝ} {ζ : Z → ℝ≥0∞} {p : Z × HistorySpace 0 0}
    {x : Fin mL → ℝ} {y : Fin mR → ℝ}
    (hx : ∀ i, x i ≤ 0) (hy : ∀ j, 0 ≤ y j) (hxs : StrictAnti x) (hys : StrictMono y)
    (hg : IsGood47 W VL VR ζ p) (he : IsRegularDriver ((fun t => W t p.1), ζ p.1))
    {s : ℝ≥0} (hs : 0 < s) :
    StrictAnti (recordXL s x (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1))) ∧
      StrictMono (recordXR s y (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1))) := by
  classical
  have hr := eqOn_rdrv_fDrv (s := s) hg he
  obtain ⟨htr, hH⟩ := exists_flowTrace hg
  have hH' : ∀ r ∈ Ioc (0 : ℝ) s, seedLine ζ W p.1 r ∈ H := fun r hr => hH r hr.1
  have hal := CrossRestart.alive_of_mem_H htr hH' (continuous_fDrv hg) (fDrv_zero hg) s.coe_nonneg
  have hal' := CrossRestart.alive_neg_of_mem_H htr hH' (continuous_fDrv hg) (fDrv_zero hg) s.coe_nonneg
  have hL : ∀ a, 0 < a → MartChar.RealFlow.Alive
      (rdrv (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1))) a s :=
    fun a ha => (Sec7.Lemma71B.alive_congr hr).2 (hal a ha)
  have hR : ∀ a, 0 < a → MartChar.RealFlow.Alive
      (fun t => -rdrv (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1)) t) a s :=
    fun a ha => (Sec7.Lemma71B.alive_congr (fun t ht => congrArg Neg.neg (hr ht))).2 (hal' a ha)
  have hj := recordGaps_recOf hg he hs
  rw [recordXL, recordXR, ite_eq_left hj, ite_eq_left hj]
  exact ⟨CrossCond.StagedRep.strictAnti_snoc
      (fun i j hij => CrossCond.StagedRep.psiL_lt_psiL (continuous_rdrv _) s.coe_nonneg hL hj.1
        (hxs hij) (hx i))
      (fun i => CrossCond.StagedRep.junL_lt_psiL (continuous_rdrv _) s.coe_nonneg hL hj.1 (hx i)),
    CrossCond.StagedRep.strictMono_snoc
      (fun i j hij => CrossCond.StagedRep.psiR_lt_psiR (continuous_rdrv _) s.coe_nonneg hR hj.2
        (hys hij) (hy i))
      (fun i => CrossCond.StagedRep.psiR_lt_junR (continuous_rdrv _) s.coe_nonneg hR hj.2 (hy i))⟩

end InteractingSLE.Sec5.CfNext
