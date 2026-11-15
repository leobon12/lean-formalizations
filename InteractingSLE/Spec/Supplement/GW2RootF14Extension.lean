/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcModel
import InteractingSLE.Spec.Sec5.Prop513Bridge
import InteractingSLE.Spec.Supplement.GW2RootE13Clock

/-!
# Complete deterministic models of protected finite trace prefixes

Packet PROVE-T14-GW2ROOT2. This is an adapter to the existing inverse-chart
slit extension in `ReverseArc.exists_global_model`. The original driver
and trace need exist only before their lifetime. No stochastic law is
asserted for their deterministic continuations.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootF14

/-- A protected finite prefix has a complete generating-trace model
agreeing with both the driver and the trace beyond the prescribed cutoff. -/
theorem exists_complete_prefix_model {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < T) :
    ∃ (w' : ℝ≥0 → ℝ) (η' : ℝ≥0 → ℂ) (b : ℝ≥0), q < b ∧
      Continuous w' ∧ w' 0 = 0 ∧ IsGeneratingTrace w' ⊤ η' ∧
      EqOn w' w (Icc 0 b) ∧ EqOn η' η (Icc 0 b) := by
  obtain ⟨W, γ, b, hqb, hW, hW0, hγ, heW, heγ⟩ :=
    Sec7.ReverseArc.exists_global_model hη hw hw0 hq
  have hb : 0 ≤ b := q.coe_nonneg.trans hqb.le
  refine ⟨(fun t => W t), (fun t => γ t), ⟨b, hb⟩, ?_,
    hW.comp NNReal.continuous_coe, ?_, Sec5.Prop513Bridge.generatingTrace_of_loewner hγ, ?_, ?_⟩
  · exact_mod_cast hqb
  · simpa only [NNReal.coe_zero] using hW0
  · intro r hr
    simpa only [Real.toNNReal_coe] using heW r ⟨r.coe_nonneg, NNReal.coe_le_coe.mpr hr.2⟩
  · intro r hr
    simpa only [Real.toNNReal_coe] using heγ r ⟨r.coe_nonneg, NNReal.coe_le_coe.mpr hr.2⟩

/-- Prefix agreement through a strictly later buffer identifies the hull,
without any global driver continuity hypothesis. -/
theorem fwdHull_eq_of_prefix_eq {w w' : ℝ≥0 → ℝ} {b t : ℝ≥0}
    (he : EqOn w w' (Icc 0 b)) (ht : t < b) :
    QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t =
      QuantumZipper.fwdHull (fun r : ℝ => w' r.toNNReal) t := by
  apply fwdHull_eq_of_eqOn t.coe_nonneg (NNReal.coe_lt_coe.mpr ht)
  intro r hr
  exact he ⟨zero_le, Real.toNNReal_le_iff_le_coe.mpr hr.2⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootF14
