/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Contact
import InteractingSLE.Spec.Supplement.GB6VersionRule

/-!
# Measurable positive physical buffers strictly before recorded contact

Packet PROVE-T14-GW2ROOT2. Reuse GB6's positive-level stopping rule on
the actual physical separation gauge. A separate finite cap permits
strict localization inside the recorded physical lifetime.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG28

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.RelDrv.Version

/-- The geometric failure buffer: a positive-level separation stop,
also capped at the specified finite physical time `b`. -/
def contactBuffer (s v b : ℝ≥0) (m : ℕ) (p : RecData × RecData) : ℝ≥0 :=
  min b (localStop (fun t => recordSeparation s v t p) m)

theorem measurable_contactBuffer (s v b : ℝ≥0) (m : ℕ) :
    Measurable (contactBuffer s v b m) := by
  have hm : Measurable fun p => localStop (fun t => recordSeparation s v t p) m :=
    measurable_gaugeStop (fun t => measurable_recordSeparation s v t)
      (fun p => continuous_recordSeparation s v p)
      (((measurable_recordSeparation s v 0).div_const 2).min measurable_const) (m + 1)
  exact measurable_const.min hm

theorem contactBuffer_le (s v b : ℝ≥0) (m : ℕ) (p : RecData × RecData) :
    contactBuffer s v b m p ≤ b := min_le_left _ _

/-- Every buffer is positive and strictly before contact for a recorded
trace starting at zero. The geometric conclusions are proved, not inputs. -/
theorem contactBuffer_spec (s v b : ℝ≥0) (m : ℕ) (p : RecData × RecData)
    (hs : 0 < s) (hb : 0 < b) (h0 : frozenTraceRead v p.2 0 = 0) :
    0 < contactBuffer s v b m p ∧
      (contactBuffer s v b m p : ℝ≥0∞) < recordContact s v p := by
  have hg0 : 0 < recordSeparation s v 0 p := by
    rw [recordSeparation_zero s v p h0]
    exact zero_lt_one
  have hpos := localStop_pos (continuous_recordSeparation s v p) hg0 m
  have hlt := localStop_lt (continuous_recordSeparation s v p) hg0
    (fun T hT => recordSeparation_eq_zero_at_contact s v p hs hT) m
  exact ⟨lt_min hb hpos,
    (ENNReal.coe_le_coe.mpr (min_le_right _ _)).trans_lt hlt⟩

/-- Every compact pre-contact interval below the finite cap lies before
some buffer. There is no assumed exhaustion or positive contact horizon. -/
theorem exists_lt_contactBuffer (s v b t : ℝ≥0) (p : RecData × RecData)
    (htb : t < b) (ht : (t : ℝ≥0∞) < recordContact s v p) :
    ∃ m : ℕ, t < contactBuffer s v b m p := by
  obtain ⟨m, hm⟩ := exists_lt_localStop (continuous_recordSeparation s v p)
    (fun u hu => recordSeparation_pos s v u p ((ENNReal.coe_le_coe.mpr hu).trans_lt ht))
  exact ⟨m, lt_min htb hm⟩

section Stage

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord)
  {Ω : Type u} (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
  (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (spec : ExplSpec) (n : ℕ)

/-- The failure buffer is known from the exact retained stage records. -/
theorem measurable_stageSigma_contactBuffer (j : Fin n) (v b : ℝ≥0) (m : ℕ) :
    Measurable[stageSigma hκ h12p βA c₀ h s W ζ spec n] (fun ω =>
      contactBuffer s v b m (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h spec j ω)) :=
  (measurable_contactBuffer s v b m).comp
    ((measurable_fst.comp (comap_measurable
      (stageMap hκ h12p βA c₀ h s W ζ spec n))).prodMk
        (RootU19.measurable_stageSigma_stopRec hκ h12p βA c₀ h s W ζ spec n j))

end Stage

end InteractingSLE.Theorem14.GW2TipSystem.RootG28
