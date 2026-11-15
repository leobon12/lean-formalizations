/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6VersionRule
import InteractingSLE.Spec.ZhanGT4.A1RefCDLive
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit

/-!
# Freezing a measurable local driver

Progressive regularization, already used in A.1, makes random-time evaluation
measurable. The original driver is needed only before its lifetime. Freezing
strictly before that lifetime preserves hulls even at the stopping endpoint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.RelDrv.Version

/-- A local driver frozen at a finite time. -/
def freeze {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (v : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  D (min t (v ω)) ω

theorem freeze_eq {Ω : Type*} {D : ℝ≥0 → Ω → ℝ} {v : Ω → ℝ≥0} {t : ℝ≥0} {ω : Ω}
    (ht : t ≤ v ω) : freeze D v t ω = D t ω := by
  rw [freeze, min_eq_left ht]

theorem freeze_after {Ω : Type*} {D : ℝ≥0 → Ω → ℝ} {v : Ω → ℝ≥0} {t : ℝ≥0} {ω : Ω}
    (ht : v ω ≤ t) : freeze D v t ω = freeze D v (v ω) ω := by
  simp only [freeze, min_eq_right ht, min_self]

theorem continuous_freeze {Ω : Type*} {D : ℝ≥0 → Ω → ℝ} {v : Ω → ℝ≥0} {L : Ω → ℝ≥0∞}
    (hc : ∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < L ω})
    (hv : ∀ ω, (v ω : ℝ≥0∞) < L ω) (ω : Ω) : Continuous (freeze D v · ω) :=
  (hc ω).comp_continuous (continuous_id.min continuous_const)
    (fun u => (ENNReal.coe_le_coe.2 (min_le_right u (v ω))).trans_lt (hv ω))

theorem measurable_freeze {Ω : Type*} {mΩ : MeasurableSpace Ω} {D : ℝ≥0 → Ω → ℝ}
    {v : Ω → ℝ≥0} {L : Ω → ℝ≥0∞}
    (hD : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) L D)
    (hc : ∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < L ω})
    (hm : Measurable v) (hv : ∀ ω, (v ω : ℝ≥0∞) < L ω) (t : ℝ≥0) :
    Measurable (freeze D v t) := by
  let 𝓕 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  have hs : IsStoppingTime 𝓕 fun ω => ((min t (v ω) : ℝ≥0) : WithTop ℝ≥0) := by
    intro u
    change MeasurableSet[mΩ] {ω | ((min t (v ω) : ℝ≥0) : WithTop ℝ≥0) ≤ u}
    simpa only [WithTop.coe_le_coe] using
      (measurableSet_le (measurable_const.min hm) measurable_const)
  have hp := Sec2.Restart.measurable_eval_stop (Sec2.Restart.isStronglyProgressive_progVersion hD) hs
  have he : (fun ω => Sec2.Restart.progVersion L D (min t (v ω)) ω) = freeze D v t := by
    funext ω
    exact Sec2.Restart.progVersion_eq (hc ω)
      ((ENNReal.coe_le_coe.2 (min_le_right t (v ω))).trans_lt (hv ω))
  rw [he] at hp
  exact hp.mono hs.measurableSpace_le le_rfl

/-- Freezing before the lifetime preserves the hull at every earlier time,
including the time at which the driver is frozen. -/
theorem fwdHull_freeze_eq {d : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    (hc : ContinuousOn d {u | (u : ℝ≥0∞) < L}) {v : ℝ≥0} (hv : (v : ℝ≥0∞) < L)
    {a : ℝ} (ha : 0 ≤ a) (hav : a ≤ v) :
    QuantumZipper.fwdHull (fun r : ℝ => d (min r.toNNReal v)) a =
      QuantumZipper.fwdHull (fun r : ℝ => d r.toNNReal) a := by
  obtain ⟨q, hvq, hqL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hv
  have hvq' : v < q := ENNReal.coe_lt_coe.1 hvq
  have hqc : Continuous (fun u : ℝ≥0 => d (min u q)) :=
    hc.comp_continuous (continuous_id.min continuous_const)
      (fun u => (ENNReal.coe_le_coe.2 (min_le_right u q)).trans_lt hqL)
  have hvc : Continuous (fun u : ℝ≥0 => d (min u v)) :=
    hc.comp_continuous (continuous_id.min continuous_const)
      (fun u => (ENNReal.coe_le_coe.2 (min_le_right u v)).trans_lt hv)
  calc
    QuantumZipper.fwdHull (fun r : ℝ => d (min r.toNNReal v)) a =
        QuantumZipper.fwdHull (fun r : ℝ => d (min r.toNNReal q)) a := by
      apply YuanCorollary13.fwdHull_eq_of_eqOn_Icc
        (hvc.comp continuous_real_toNNReal) (hqc.comp continuous_real_toNNReal) ha
      intro r hr
      have hrv : r.toNNReal ≤ v := Real.toNNReal_le_iff_le_coe.2 (hr.2.trans hav)
      change d (min r.toNNReal v) = d (min r.toNNReal q)
      rw [min_eq_left hrv, min_eq_left (hrv.trans hvq'.le)]
    _ = QuantumZipper.fwdHull (fun r : ℝ => d r.toNNReal) a := by
      apply fwdHull_eq_of_eqOn ha (t₂ := (q : ℝ)) (hav.trans_lt (by exact_mod_cast hvq'))
      intro r hr
      rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]

end InteractingSLE.Supp8.GB6.RelDrv.Version
