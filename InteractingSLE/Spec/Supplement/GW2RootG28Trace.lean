/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Read
import InteractingSLE.Spec.Restart.ChartSpace

/-!
# Continuous physical prefix readers on the full stopped-record space

Packet PROVE-T14-GW2ROOT2. Reuse the restart-space continuous decoder
on the clamped physical trace. Every record gives a continuous path;
on a live original prefix this is exactly its frozen generating trace.
No measurable good-source event or trace witness is selected.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG28

open Exist Staged StagedLaw Restart

/-- The total continuous decoder of the physical trace frozen at `v`. -/
def frozenTraceRead (v : ℝ≥0) (r : RecData) : ℝ≥0 → ℂ :=
  decPath (encPath (fun t => RootU19.recordTrace r (min t v)) ⊤)

/-- Every record, including an irregular one, yields a continuous reader. -/
theorem continuous_frozenTraceRead (v : ℝ≥0) (r : RecData) :
    Continuous (frozenTraceRead v r) := by
  apply continuousOn_univ.mp
  exact (continuousOn_decPath _).mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top

/-- The continuous reader is Borel at every physical time. -/
theorem measurable_frozenTraceRead (v t : ℝ≥0) :
    Measurable fun r => frozenTraceRead v r t :=
  (measurable_decPath t).comp (measurable_encPath
    (fun q => (measurable_pi_apply (min q v)).comp RootU19.measurable_recordTrace)
    measurable_const)

/-- Live finite recording reconstructs the actual entire frozen prefix.
Only the original generating trace and regular driver are inputs. -/
theorem frozenTraceRead_recOf_eq {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 e.2 γ)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < e.2) :
    frozenTraceRead v (recOf (v : ℝ≥0∞) e) = fun t => γ (min t v) := by
  have hc : ContinuousOn e.1 {q | (q : ℝ≥0∞) ≤ min (v : ℝ≥0∞) e.2} :=
    he.1.mono fun q hq => (hq.trans (min_le_left _ _)).trans_lt hv
  have hg := LP.isGeneratingTrace_mono hγ (min_le_right (v : ℝ≥0∞) e.2)
  have hread : (fun t => RootU19.recordTrace (recOf (v : ℝ≥0∞) e) (min t v)) =
      fun t => γ (min t v) := by
    funext t
    exact RootU19.recordTrace_recOf_eq he
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)) hc hg
      (le_min (ENNReal.coe_le_coe.mpr (min_le_right t v))
        ((ENNReal.coe_le_coe.mpr (min_le_right t v)).trans hv.le))
  have hcont : Continuous fun t => γ (min t v) :=
    hγ.2.1.comp_continuous (continuous_id.min continuous_const)
      (fun t => (ENNReal.coe_le_coe.mpr (min_le_right t v)).trans hv.le)
  funext t
  rw [frozenTraceRead, hread]
  exact decPath_encPath hcont.continuousOn le_top

/-- On the original continuous infinite counterflow sample, its stopped
record reconstructs precisely the retained trace, frozen at the stop. -/
theorem frozenTraceRead_cfRec_eq {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (ω : Ω) (hW : Continuous (W · ω))
    (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (W · ω) ⊤ α) :
    frozenTraceRead s (cfRec s W ζ ω) = fun t => α (min t s) := by
  change frozenTraceRead s (recOf (s : ℝ≥0∞) (GW2JointKernel.cfE s W ζ ω)) = _
  have he : GW2JointKernel.cfE s W ζ ω = ((W · ω), ⊤) := by
    exact GW2JointKernel.cfE_eq s hζ hW0 hW
  have hreg : IsRegularDriver (GW2JointKernel.cfE s W ζ ω) :=
    StagedReg.isRegularDriver_regularize _ _
  apply frozenTraceRead_recOf_eq hreg
  · rwa [he]
  · rw [he]
    exact ENNReal.coe_lt_top

end InteractingSLE.Theorem14.GW2TipSystem.RootG28
