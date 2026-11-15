/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Read
import InteractingSLE.Spec.Supplement.GW2RootU19Adapted

/-!
# Next-piece causality across different switched candidate programs

Packet PROVE-T14-GW2ROOT2. Changing the last prescribed recording time
does not change the next canonical driver or lifetime, at any sample.
Its whole frozen driving prefix and its canonical tip at a query are
measurable in the other candidate program's retained stage whenever
that program records through the query. No trace regularity event or
continuous-decoder fallback is used in these exact assertions.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24

/-- The last appended instruction has its prescribed angle. -/
theorem specAngle_last (x θ : ℝ) (l : List (ℝ × ℝ≥0)) (q : ℝ≥0) :
    specAngle (schedSpec x (l ++ [(θ, q)])) l.length = θ := by
  have hi := isFlowProg_scheduleProgram 0 (l ++ [(θ, q)]) l.length
    (by rw [length_scheduleProgram, List.length_append, List.length_singleton]; omega)
  change instrAngle (schedSpec x (l ++ [(θ, q)])) l.length = θ
  simp only [instrAngle, schedSpec, hi]
  simp only [schedAngle, List.getD_append_right _ _ _ _ le_rfl,
    Nat.sub_self, List.getD_cons_zero]

/-- At every sample, the next canonical piece after an arbitrary
switched history is independent of its own proposed recording cutoff. -/
theorem canonical_next_independent_time {κ : ℝ} (hκ : 0 < κ)
    (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
    (c₀ : BoundaryWord) {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)
    (x θ : ℝ) (l : List (ℝ × ℝ≥0)) (q q' : ℝ≥0) (ω : Ω) :
    canonSpecFam hκ h12p βA c₀ h (schedSpec x (l ++ [(θ, q)])) l.length ω =
      canonSpecFam hκ h12p βA c₀ h (schedSpec x (l ++ [(θ, q')])) l.length ω := by
  have hs := canonState_congr₂ hκ h12p βA c₀ x (h ω) (k := l.length)
    (fun j hj => (specAngle_schedSpec_append x (l := l) (θ, q) hj).trans
      (specAngle_schedSpec_append x (l := l) (θ, q') hj).symm)
    (fun j hj => (specDelta_schedSpec_append x (l := l) (θ, q) hj).trans
      (specDelta_schedSpec_append x (l := l) (θ, q') hj).symm)
  change canonDrive hκ h12p βA c₀ x _ _ (h ω) l.length =
    canonDrive hκ h12p βA c₀ x _ _ (h ω) l.length
  simp only [canonDrive, hs, specAngle_last]

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The actual next driver and canonical tip of one proposed cutoff
are observable in the retained stage of another proposed cutoff.
This compares different programs and holds on exceptional samples too. -/
theorem measurable_next_observation_other_cutoff (c : SourceData Ω)
    (x θ : ℝ) (l : List (ℝ × ℝ≥0)) (q q' t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ specDelta (schedSpec x (l ++ [(θ, q')])) l.length) :
    Measurable[stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec x (l ++ [(θ, q')])) (l.length + 1)] (fun ω =>
      ((canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec x (l ++ [(θ, q)])) l.length ω).1 t,
        LP.traceAt t (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec x (l ++ [(θ, q)])) l.length ω).1)) := by
  have hm := RootU19.measurable_stageSigma_canonical_observation
    c.hκ c.h12p c.βA c.c₀ c.h c.hβA.1 c.hh.1 c.s c.W c.ζ c.hcf
    (schedSpec x (l ++ [(θ, q')])) (l.length + 1) ⟨l.length, Nat.lt_succ_self _⟩ t ht
  have heq : (fun ω => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
      (schedSpec x (l ++ [(θ, q)])) l.length ω) =
      (fun ω => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec x (l ++ [(θ, q')])) l.length ω) :=
    funext (canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h x θ l q q')
  simp_rw [congrFun heq]
  exact hm

/-- The entire driving prefix frozen at the query is observable in
the other candidate's retained stage. This is an exact all-sample
causality assertion, not merely an identity on a regular source event. -/
theorem measurable_next_frozenDriver_other_cutoff (c : SourceData Ω)
    (x θ : ℝ) (l : List (ℝ × ℝ≥0)) (q q' t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤ specDelta (schedSpec x (l ++ [(θ, q')])) l.length) :
    Measurable[stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec x (l ++ [(θ, q')])) (l.length + 1)] (fun ω => fun u : ℝ≥0 =>
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec x (l ++ [(θ, q)])) l.length ω).1 (min u t)) := by
  apply (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ)
    (stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec x (l ++ [(θ, q')])) (l.length + 1)) (fun _ => inferInstance) _).mpr
  intro u
  exact measurable_fst.comp (measurable_next_observation_other_cutoff c x θ l q q'
    (min u t) ((ENNReal.coe_le_coe.mpr (min_le_right u t)).trans ht))

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
