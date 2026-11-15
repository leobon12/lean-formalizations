/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootB23Normalized

/-!
# Actual relative observations at a random capacity

Packet PROVE-T14-GW2ROOT2. The inverse clock is a countable supremum,
the hull reader uses clamped dyadic trace values, and the driver reader
uses countably many hull evaluations. These formulas prove measurability
at random capacity on the entire record space, including exceptional samples.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD25

open Exist.StagedLaw Restart Supp8.GB6 RootB23

variable {Ω : Type*} [MeasurableSpace Ω]
  {p : Ω → RecData × RecData} (hp : Measurable p)
  {u : Ω → ℝ≥0} (hu : Measurable u)

include hp hu

/-- The literal rational-supremum inverse remains measurable at a random level. -/
theorem measurable_forwardClockInverse_random (s v : ℝ≥0) :
    Measurable fun ω => RootZ21.forwardClockInverse s v (u ω) (p ω) := by
  classical
  unfold RootZ21.forwardClockInverse invClock
  refine Measurable.iSup fun q : ℚ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_lt ((RootZ21.measurable_forwardCapacity s _).comp hp)
      (measurable_coe_nnreal_real.comp hu)))

/-- Random relative time is read by the actual physical inverse and boundary chart. -/
theorem measurable_relativeTipRead_random (s v : ℝ≥0) :
    Measurable fun ω => RootA22.relativeTipRead s v (u ω) (p ω) :=
  (RootA22.measurable_boundaryRead s).comp ((measurable_fst.comp hp).prodMk
    (RootA22.measurable_physicalTipRead.comp ((measurable_snd.comp hp).prodMk
      (measurable_forwardClockInverse_random hp hu s v))))

/-- The clamped trace-hull formula is measurable at a random capacity. -/
theorem measurable_relativeTraceHull_random (s v : ℝ≥0) :
    Measurable[_, hittingSigma] fun ω =>
      traceHullRead (fun t => RootA22.relativeTipRead s v t (p ω)) (u ω) := by
  have hc := Sec5.Aux61SlitW.measurable_closure_range
    (fun j : ℕ × ℕ => measurable_relativeTipRead_random hp
      (measurable_const.min hu) s v (u := fun ω => min (LawUnique.dyadicTime j) (u ω)))
  apply Restart.FlowStopIdentCMI.measurable_hullFillReader.comp
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have he : (fun ω =>
      closure (range fun j : ℕ × ℕ =>
        RootA22.relativeTipRead s v (min (LawUnique.dyadicTime j) (u ω)) (p ω)) ∩ H) ⁻¹'
        {A : Set ℂ | (A ∩ U).Nonempty} =
      (fun ω => closure (range fun j : ℕ × ℕ =>
        RootA22.relativeTipRead s v (min (LawUnique.dyadicTime j) (u ω)) (p ω))) ⁻¹'
          {A : Set ℂ | (A ∩ U).Nonempty} := by
    ext ω
    constructor
    · rintro ⟨z, ⟨hz, _⟩, hzU⟩
      exact ⟨z, hz, hzU⟩
    · rintro ⟨z, hz, hzU⟩
      exact ⟨z, ⟨hz, hUH hzU⟩, hzU⟩
  rw [he]
  exact hc (LocalSets.measurableSet_hitting hU hUH)

/-- The actual hull-to-driver quotient also permits a random evaluation time. -/
theorem measurable_relativeDriverRead_random (s v : ℝ≥0) :
    Measurable fun ω => relativeDriverRead s v (u ω) (p ω) := by
  classical
  unfold relativeDriverRead traceDriverRead GW2JDetR4.hullDriverRead
  refine Measurable.ite (hu (measurableSet_singleton 0)) measurable_const ?_
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro N
  apply StronglyMeasurable.limUnder
  intro k
  have h1 := (GW2JDetR4.measurable_hullMapRead (Sec7.Lemma71C.zPt N)).comp
    (measurable_relativeTraceHull_random hp hu s v)
  have htime : Measurable fun ω => ((u ω : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal :=
    ((measurable_coe_nnreal_real.comp hu).sub_const _).real_toNNReal
  have h2 := (GW2JDetR4.measurable_hullMapRead (Sec7.Lemma71C.zPt N)).comp
    (measurable_relativeTraceHull_random hp htime s v)
  exact (Complex.measurable_re.comp (h1.sub
    (measurable_const.div (measurable_const.mul (h1.sub h2))))).stronglyMeasurable

theorem measurable_scaledRelativeObservationRead_random (a s v : ℝ≥0) :
    Measurable fun ω => scaledRelativeObservationRead a s v (u ω) (p ω) := by
  have ht : Measurable fun ω => u ω / a ^ 2 := hu.div_const _
  exact (measurable_const.mul (measurable_relativeDriverRead_random hp ht s v)).prodMk
    (measurable_const.mul (measurable_relativeTipRead_random hp ht s v))

end InteractingSLE.Theorem14.GW2TipSystem.RootD25
