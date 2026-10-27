import MatedCRTHarmonic.Canon.Density
import MatedCRTHarmonic.Canon.ClockMeasurable
import MatedCRTHarmonic.GMS4c.Lemma49Observable
import MatedCRTHarmonic.GMS4c.Transfer
import MatedCRTHarmonic.GMS4F.RealObservable
import MatedCRTHarmonic.GMS4b.BundleAdapter
import MatedCRTHarmonic.GMS4b.UStarMoments
import MatedCRTHarmonic.GMS4b.Interfaces
import MatedCRTHarmonic.GMS4b.Packing
import MatedCRTHarmonic.GMSLemma27.CellModel
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import MatedCRTHarmonic.CellScaling.ConeDefs
import MatedCRTHarmonic.GMCFacts.ConeCompare
import MatedCRTHarmonic.LQGCoord.Transform
import MatedCRTHarmonic.CellScaling.ZeroConeScalingCells

/-!
# Real and measurable views of the canonical localized observables

The geometric degrees retain `ℕ∞` values. Their natural representatives are
total and agree with the geometry on the finite event. The local event uses
the actual two field averages at the radius in [18] (4.22).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The radius of the two conditioning circle averages in (4.22). -/
def conditioningRadius (ε q ζ : ℝ) : ℝ := ε ^ (q - 4 * ζ)

/-- The circle average of the IG field that actually drives the frozen
space-filling curve. The shared phase is a separate random coordinate. -/
def actualIGAverage (hIG₀ : Ω → MatedCRT.Field) (U : Ω → ℝ)
    (r : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  LQGMetric.circleAvg (hIG₀ ω) r z + U ω

theorem aemeasurable_actualIGAverage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (r : ℝ) (z : ℂ) :
    AEMeasurable (actualIGAverage hIG₀ U r z) P :=
  ((LQGMetric.measurable_circleAvg_left r z).comp
    D.igField.1.1.measurable).aemeasurable.add (aemeasurable_phase D hγ)

/-- At positive radius the explicit phase-aware average is the actual circle
average of the IG field `hIG₀ + U` which drives `ηL`. -/
theorem ae_actualIGAverage_eq_fullIG_circleAvg
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, actualIGAverage hIG₀ U r z ω =
      LQGMetric.circleAvg (LQGMetric.addConst (hIG₀ ω) (U ω)) r z := by
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst D.igField.1.1 z hr]
    with ω hω
  exact (hω (U ω)).symm

/-- The phase-aware local observation required by the frozen IG coupling:
restricted LQG field, restricted normalized IG field, and shared phase. -/
def phaseAwareObservation (V : TopologicalSpace.Opens ℂ)
    (h hIG₀ : Ω → MatedCRT.Field) (U : Ω → ℝ) (ω : Ω) :
    GMS4c.LocalFieldPair V × ℝ :=
  (GMS4c.localFieldPair V h hIG₀ ω, U ω)

theorem aemeasurable_phaseAwareObservation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (h : Ω → MatedCRT.Field)
    (hh : AEMeasurable h P) :
    AEMeasurable (phaseAwareObservation V h hIG₀ U) P := by
  exact (((LQGMetric.measurable_restrictTo V).comp_aemeasurable hh).prodMk
    ((LQGMetric.measurable_restrictTo V).comp
      D.igField.1.1.measurable).aemeasurable).prodMk (aemeasurable_phase D hγ)

theorem aemeasurable_conePhaseObservation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : TopologicalSpace.Opens ℂ) :
    AEMeasurable (phaseAwareObservation V
      (fun ω => (coneSample D hγ ω).field) hIG₀ U) P :=
  aemeasurable_phaseAwareObservation D hγ V _ (aemeasurable_cone_field D hγ)

theorem aemeasurable_referencePhaseObservation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : TopologicalSpace.Opens ℂ) :
    AEMeasurable (phaseAwareObservation V
      (fun ω => (referenceSample D hγ ω).zeroConeField) hIG₀ U) P :=
  aemeasurable_phaseAwareObservation D hγ V _ (aemeasurable_reference_field D hγ)

theorem aemeasurable_wholePlanePhaseObservation
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : TopologicalSpace.Opens ℂ) :
    AEMeasurable (phaseAwareObservation V
      (fun ω => (referenceSample D hγ ω).wholePlaneGFF) hIG₀ U) P :=
  aemeasurable_phaseAwareObservation D hγ V _
    (measurable_normalizedWholePlane D).aemeasurable

/-- Natural and real representatives of the geometric local quantities. -/
structure RealLocalPoint where
  areaRatio : ℝ
  degreeIn : ℕ
  degreeOut : ℕ
  uStar : ℝ

def realLocalPoint (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) : RealLocalPoint :=
  { areaRatio := GMS4F.realAreaRatio ε c z
    degreeIn := GMS4F.natDegreeIn ε c z
    degreeOut := GMS4F.natDegreeOut ε c z
    uStar := GMS4F.realUStar ε c z }

theorem realLocalPoint_formula (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) :
    (realLocalPoint ε c z).uStar = (realLocalPoint ε c z).areaRatio *
      (((realLocalPoint ε c z).degreeIn +
        (realLocalPoint ε c z).degreeOut : ℕ) : ℝ) := rfl

/-- Identification with the extended source objects on the exact finite
geometric event. This is the adapter needed before a natural-valued view. -/
theorem realLocalPoint_eq_geometric_of_finite
    {ε : ℝ} {c : C(ℝ, ℂ)} {z : ℂ}
    (hDA : GMS4b.areaRatio ε c z ≠ ⊤)
    (hIn : GMS4b.degreeIn ε c z ≠ ⊤)
    (hOut : GMS4b.degreeOut ε c z ≠ ⊤) :
    ENNReal.ofReal (realLocalPoint ε c z).areaRatio = (localPoint ε c z).DA ∧
    (((realLocalPoint ε c z).degreeIn : ℕ) : ℕ∞) = (localPoint ε c z).degreeIn ∧
    (((realLocalPoint ε c z).degreeOut : ℕ) : ℕ∞) =
      (localPoint ε c z).degreeOut ∧
    ENNReal.ofReal (realLocalPoint ε c z).uStar = (localPoint ε c z).uStar := by
  refine ⟨ENNReal.ofReal_toReal hDA, ENat.natCast_toNat_eq_self.mpr hIn,
    ENat.natCast_toNat_eq_self.mpr hOut, ?_⟩
  exact GMS4F.ofReal_realUStar_eq_geometric hDA hIn hOut

def coneConditioningInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) :
    GMS4c.Lemma49Input :=
  (η ω, (LQGMetric.circleAvg (coneSample D hγ ω).field
      (conditioningRadius ε q ζ) z,
    actualIGAverage hIG₀ U (conditioningRadius ε q ζ) z ω))

def referenceConditioningInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω) :
    GMS4c.Lemma49Input :=
  (η₀ ω, (LQGMetric.circleAvg (referenceSample D hγ ω).zeroConeField
      (conditioningRadius ε q ζ) z,
    actualIGAverage hIG₀ U (conditioningRadius ε q ζ) z ω))

/-- [18] (4.22), evaluated on the cone data. -/
def coneLocalEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) : Set Ω :=
  (coneConditioningInput D hγ ε q ζ z) ⁻¹' GMS4c.lemma49Event ε q ζ z

/-- The same (4.22) event on the zero-cone reference data. -/
def referenceLocalEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) : Set Ω :=
  (referenceConditioningInput D hγ ε q ζ z) ⁻¹' GMS4c.lemma49Event ε q ζ z

theorem aemeasurable_coneConditioningInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) :
    AEMeasurable (coneConditioningInput D hγ ε q ζ z) P := by
  have hfield : AEMeasurable (fun ω => LQGMetric.circleAvg
      (coneSample D hγ ω).field (conditioningRadius ε q ζ) z) P :=
    (LQGMetric.measurable_circleAvg_left _ _).comp_aemeasurable
      (aemeasurable_cone_field D hγ)
  have hig := aemeasurable_actualIGAverage D hγ (conditioningRadius ε q ζ) z
  exact D.measurable_curves.2.1.aemeasurable.prodMk
    (hfield.prodMk hig)

theorem nullMeasurableSet_coneLocalEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε q ζ : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    NullMeasurableSet (coneLocalEvent D hγ ε q ζ z) P :=
  (aemeasurable_coneConditioningInput D hγ ε q ζ z).nullMeasurableSet_preimage
    (GMS4c.measurableSet_lemma49Event hε z)

/-- On the actual local event, the finite degree cap rules out infinite
geometric in- and out-degree. -/
theorem coneLocalEvent_degrees_finite
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω)
    (hω : ω ∈ coneLocalEvent D hγ ε q ζ z) :
    GMS4b.degreeIn ε (η ω) z ≠ ⊤ ∧ GMS4b.degreeOut ε (η ω) z ≠ ⊤ := by
  have hcap := hω.2.1
  change (((GMS4b.degreeIn ε (η ω) z + GMS4b.degreeOut ε (η ω) z : ℕ∞) :
    ℝ≥0∞)) ≤ ENNReal.ofReal (ε ^ (-ζ)) at hcap
  constructor
  · intro hi
    simp [hi] at hcap
  · intro ho
    simp [ho] at hcap

/-- On the local event, the natural representatives agree exactly with
the canonical degrees. The area ratio and density also agree if the ratio is
finite. -/
theorem realLocalPoint_eq_geometric_on_coneLocalEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (ω : Ω)
    (hω : ω ∈ coneLocalEvent D hγ ε q ζ z)
    (hDA : GMS4b.areaRatio ε (η ω) z ≠ ⊤) :
    ENNReal.ofReal (realLocalPoint ε (η ω) z).areaRatio =
        (coneLocalPoint D hγ ε ω z).DA ∧
    (((realLocalPoint ε (η ω) z).degreeIn : ℕ) : ℕ∞) =
        (coneLocalPoint D hγ ε ω z).degreeIn ∧
    (((realLocalPoint ε (η ω) z).degreeOut : ℕ) : ℕ∞) =
        (coneLocalPoint D hγ ε ω z).degreeOut ∧
    ENNReal.ofReal (realLocalPoint ε (η ω) z).uStar =
        (coneLocalPoint D hγ ε ω z).uStar := by
  obtain ⟨hIn, hOut⟩ := coneLocalEvent_degrees_finite D hγ ε q ζ z ω hω
  exact realLocalPoint_eq_geometric_of_finite hDA hIn hOut

theorem aemeasurable_referenceConditioningInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) :
    AEMeasurable (referenceConditioningInput D hγ ε q ζ z) P := by
  have hfield : AEMeasurable (fun ω => LQGMetric.circleAvg
      (referenceSample D hγ ω).zeroConeField (conditioningRadius ε q ζ) z) P :=
    (LQGMetric.measurable_circleAvg_left _ _).comp_aemeasurable
      (aemeasurable_reference_field D hγ)
  have hig := aemeasurable_actualIGAverage D hγ (conditioningRadius ε q ζ) z
  exact D.measurable_curves.2.2.1.aemeasurable.prodMk
    (hfield.prodMk hig)

theorem nullMeasurableSet_referenceLocalEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε q ζ : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    NullMeasurableSet (referenceLocalEvent D hγ ε q ζ z) P :=
  (aemeasurable_referenceConditioningInput D hγ ε q ζ z).nullMeasurableSet_preimage
    (GMS4c.measurableSet_lemma49Event hε z)

/-- Every local coordinate is jointly Borel in a measurable curve and point.
The integer index is the ceiling of the measurable first-hit time. -/
theorem measurable_localPoint_coordinates
    {T : Type} [MeasurableSpace T] (c : T → C(ℝ, ℂ)) (hc : Measurable c)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Measurable fun p : T × ℂ => (localPoint ε (c p.1) p.2).firstHit) ∧
    (Measurable fun p : T × ℂ => (localPoint ε (c p.1) p.2).selected) ∧
    (Measurable fun p : T × ℂ => (localPoint ε (c p.1) p.2).DA) ∧
    (Measurable fun p : T × ℂ => (localPoint ε (c p.1) p.2).degreeIn) ∧
    (Measurable fun p : T × ℂ => (localPoint ε (c p.1) p.2).degreeOut) ∧
    (Measurable fun p : T × ℂ => (localPoint ε (c p.1) p.2).uStar) := by
  let g : T × ℂ → C(ℝ, ℂ) × ℂ := fun p => (c p.1, p.2)
  have hg : Measurable g := (hc.comp measurable_fst).prodMk measurable_snd
  have hτ : Measurable fun p : T × ℂ => GMS4b.hitTime (c p.1) p.2 := by
    simpa only [Function.comp_def, g] using GMS4b.measurable_hitTime.comp hg
  refine ⟨hτ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Int.measurable_ceil.comp (hτ.div_const ε)
  · simpa only [localPoint, Function.comp_def, g] using
      (GMS4b.measurable_areaRatio ε).comp hg
  · simpa only [localPoint, Function.comp_def, g] using
      (GMS4b.measurable_degreeIn ε).comp hg
  · simpa only [localPoint, Function.comp_def, g] using
      (GMS4b.measurable_degreeOut hε).comp hg
  · simpa only [localPoint, Function.comp_def, g] using
      (GMS4b.measurable_uStar hε).comp hg

theorem measurable_coneLocalPoint_coordinates
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measurable fun p : Ω × ℂ => (coneLocalPoint D hγ ε p.1 p.2).firstHit) ∧
    (Measurable fun p : Ω × ℂ => (coneLocalPoint D hγ ε p.1 p.2).selected) ∧
    (Measurable fun p : Ω × ℂ => (coneLocalPoint D hγ ε p.1 p.2).DA) ∧
    (Measurable fun p : Ω × ℂ => (coneLocalPoint D hγ ε p.1 p.2).degreeIn) ∧
    (Measurable fun p : Ω × ℂ => (coneLocalPoint D hγ ε p.1 p.2).degreeOut) ∧
    (Measurable fun p : Ω × ℂ => (coneLocalPoint D hγ ε p.1 p.2).uStar) := by
  simpa only [coneLocalPoint, coneSample] using
    measurable_localPoint_coordinates η D.measurable_curves.2.1 hε

theorem measurable_referenceLocalPoint_coordinates
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measurable fun p : Ω × ℂ => (referenceLocalPoint D hγ ε p.1 p.2).firstHit) ∧
    (Measurable fun p : Ω × ℂ => (referenceLocalPoint D hγ ε p.1 p.2).selected) ∧
    (Measurable fun p : Ω × ℂ => (referenceLocalPoint D hγ ε p.1 p.2).DA) ∧
    (Measurable fun p : Ω × ℂ => (referenceLocalPoint D hγ ε p.1 p.2).degreeIn) ∧
    (Measurable fun p : Ω × ℂ => (referenceLocalPoint D hγ ε p.1 p.2).degreeOut) ∧
    (Measurable fun p : Ω × ℂ => (referenceLocalPoint D hγ ε p.1 p.2).uStar) := by
  simpa only [referenceLocalPoint, referenceSample] using
    measurable_localPoint_coordinates η₀ D.measurable_curves.2.2.1 hε

end MatedCRTHarmonic.Canon
