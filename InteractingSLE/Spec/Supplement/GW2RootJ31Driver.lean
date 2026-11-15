/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Inverse
import InteractingSLE.Spec.Supplement.GW2RootB23Driver

/-!
# Total low-arc driving readers at random capacity

Packet PROVE-T14-GW2ROOT2. These are concrete readers, not an assertion
that an exceptional record generates a Loewner trace. The driver is read
from the already constructed low-arc capacity-time tip. Random evaluations
are Borel on the whole record space.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist.StagedLaw Restart RootB23

/-- The low-arc driver reconstructed from its capacity-time tip. -/
def capacityDriverRead (x : ℝ) (s v u : ℝ≥0) (p : RecData × RecData) : ℝ :=
  traceDriverRead (fun t => RootI30.capacityTipRead x s v t p) u

variable {Ω : Type*} [MeasurableSpace Ω]
  {p : Ω → RecData × RecData} (hp : Measurable p)
  {u : Ω → ℝ≥0} (hu : Measurable u)

include hp hu

/-- Clamped dyadic hull reconstruction permits a random evaluation time. -/
theorem measurable_capacityTraceHull_random (x : ℝ) (s v : ℝ≥0) :
    Measurable[_, hittingSigma] fun ω =>
      traceHullRead (fun t => RootI30.capacityTipRead x s v t (p ω)) (u ω) := by
  have hc := Sec5.Aux61SlitW.measurable_closure_range
    (fun j : ℕ × ℕ => RootI30.measurable_capacityTipRead_random x s v hp
      (measurable_const.min hu) (u := fun ω => min (LawUnique.dyadicTime j) (u ω)))
  apply Restart.FlowStopIdentCMI.measurable_hullFillReader.comp
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have he : (fun ω =>
      closure (range fun j : ℕ × ℕ => RootI30.capacityTipRead x s v
        (min (LawUnique.dyadicTime j) (u ω)) (p ω)) ∩ H) ⁻¹'
        {A : Set ℂ | (A ∩ U).Nonempty} =
      (fun ω => closure (range fun j : ℕ × ℕ => RootI30.capacityTipRead x s v
        (min (LawUnique.dyadicTime j) (u ω)) (p ω))) ⁻¹'
          {A : Set ℂ | (A ∩ U).Nonempty} := by
    ext ω
    constructor
    · rintro ⟨z, ⟨hz, _⟩, hzU⟩
      exact ⟨z, hz, hzU⟩
    · rintro ⟨z, hz, hzU⟩
      exact ⟨z, ⟨hz, hUH hzU⟩, hzU⟩
  rw [he]
  exact hc (LocalSets.measurableSet_hitting hU hUH)

/-- The hull quotient for the low-arc tip is Borel also at random capacity. -/
theorem measurable_capacityDriverRead_random (x : ℝ) (s v : ℝ≥0) :
    Measurable fun ω => capacityDriverRead x s v (u ω) (p ω) := by
  classical
  unfold capacityDriverRead traceDriverRead GW2JDetR4.hullDriverRead
  refine Measurable.ite (hu (measurableSet_singleton 0)) measurable_const ?_
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro N
  apply StronglyMeasurable.limUnder
  intro k
  have h1 := (GW2JDetR4.measurable_hullMapRead (Sec7.Lemma71C.zPt N)).comp
    (measurable_capacityTraceHull_random hp hu x s v)
  have ht : Measurable fun ω => ((u ω : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal :=
    ((NNReal.continuous_coe.measurable.comp hu).sub_const _).real_toNNReal
  have h2 := (GW2JDetR4.measurable_hullMapRead (Sec7.Lemma71C.zPt N)).comp
    (measurable_capacityTraceHull_random hp ht x s v)
  exact (Complex.measurable_re.comp (h1.sub
    (measurable_const.div (measurable_const.mul (h1.sub h2))))).stronglyMeasurable

omit [MeasurableSpace Ω] hp hu in
/-- The reader is normalized at the initial capacity. -/
theorem capacityDriverRead_zero (x : ℝ) (s v : ℝ≥0) (p : RecData × RecData) :
    capacityDriverRead x s v 0 p = 0 := traceDriverRead_zero _

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
