/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYFillLocal

/-! # The Gaussian filled-hull limit theorem, with no residual input -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H fwdHull)

/-- Filled Loewner hulls remain local at an increasing finite limit time.
This proves the exact X-stage statement. In particular it imposes no extra
measurability hypothesis on the driver or the random times. -/
theorem cmiXHullLocalityLimitStatement : CMIXHullLocalityLimitStatement.{u} := by
  intro S mS P hP h hh W hW0 hWc s t hmono hst hlim hloc
  have hm : ∀ᵐ ω ∂P, Monotone fun n => fwdHull (Ito.rpath (W · ω)) (s n ω) :=
    Eventually.of_forall fun ω n m hnm =>
      (QuantumZipper.fwdHull_mono (W := Ito.rpath (W · ω))).1
        (NNReal.coe_le_coe.2 (hmono ω hnm))
  have hb : ∀ᵐ ω ∂P, Bornology.IsBounded (⋃ n, fwdHull (Ito.rpath (W · ω)) (s n ω)) := by
    refine Eventually.of_forall fun ω => ?_
    have hK := isHPHull_fwdHull ((hWc ω).comp continuous_real_toNNReal) (NNReal.coe_nonneg (t ω))
    exact hK.2.1.subset (iUnion_subset fun n =>
      (QuantumZipper.fwdHull_mono (W := Ito.rpath (W · ω))).1
        (NNReal.coe_le_coe.2 (hst n ω)))
  apply Coupling.IsLocalSet.congr_set (isLocalSet_fillH_iUnion hh hm hb hloc)
  filter_upwards [hlim] with ω hω
  have hzero : Ito.rpath (W · ω) 0 = 0 := by
    simpa only [Ito.rpath, Real.toNNReal_zero] using hW0 ω
  exact fwdHull_eq_fillH_iUnion (W := Ito.rpath (W · ω))
    ((hWc ω).comp continuous_real_toNNReal) hzero (fun n => hst n ω) hω

end InteractingSLE.Restart.FlowStopIdentCMI
