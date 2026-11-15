import LQGMetric.Meas.UM

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Analytic sets are universally measurable (Lusin; Choquet capacitability)

Packet PROVE-ANALYTIC-UM, the input that the W5 event of the crossing chart proposition
(`HasOrderedProperCompletions`, an `∃` over completions, so a projection) needs
(`planning/handoffs/PROVE-SUPP10-B.md` §1(b)). Infrastructure, not a frozen source-facing file.

**Nothing is reproved here.** The theorem is already proved (standard axioms only) and built in the host
libraries this workspace depends on (ruling R4):

* `QuantumZipper.Thm18Asm.G4Core.analyticSet_nullMeasurableSet`
  (`QuantumZipper/Proofs/Thm18/G4CMeasLusin.lean`): for a finite Borel measure on a Polish space,
  every analytic set (Mathlib's `MeasureTheory.AnalyticSet`) is null-measurable. Its proof is the
  classical inner approximation by compact sets (Kechris, *Classical Descriptive Set Theory*,
  Thm 21.10 via 29.7 / 30.13): `s = range f` with `f : (ℕ → ℕ) → X` continuous, bounds chosen
  recursively using continuity of outer measure along increasing unions, and compactness of the
  bounded cylinder image.
* `LQGMetric.UMeasurableSet` (`LQGMetric/Meas/UM.lean`): universal measurability (null-measurable
  for every finite measure) with its σ-algebra API and the Lusin consequences for standard Borel
  spaces (`UMeasurableSet.image`, `image_fst`, `setOf_exists`, `setOf_forall`,
  `nullMeasurableSet_preimage`).

This file collects them under project names, in the shapes the specification's events take:
an analytic set, a Borel image, an `∃`/`∀` over a standard Borel parameter, and such an event
pulled back to a probability space by an a.e.-measurable random variable.
-/

open MeasureTheory Set

namespace InteractingSLE

section Polish

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  {s : Set X}

/-- **Lusin's theorem** (Kechris 21.10): an analytic subset of a Polish space is null-measurable
for every finite Borel measure. Reused from QuantumZipper. -/
theorem analyticSet_nullMeasurableSet (hs : AnalyticSet s) (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet s μ :=
  QuantumZipper.Thm18Asm.G4Core.analyticSet_nullMeasurableSet hs μ

/-- Lusin's theorem for s-finite (in particular σ-finite) Borel measures. -/
theorem analyticSet_nullMeasurableSet_of_sFinite (hs : AnalyticSet s) (μ : Measure X)
    [SFinite μ] : NullMeasurableSet s μ :=
  QuantumZipper.Thm18Asm.G4Core.analyticSet_nullMeasurableSet_of_sFinite hs μ

/-- Analytic sets are universally measurable. -/
theorem analyticSet_uMeasurableSet (hs : AnalyticSet s) : LQGMetric.UMeasurableSet s :=
  fun μ hμ => haveI := hμ; analyticSet_nullMeasurableSet hs μ

/-- Coanalytic sets are null-measurable for every s-finite Borel measure. -/
theorem coanalyticSet_nullMeasurableSet (hs : AnalyticSet sᶜ) (μ : Measure X) [SFinite μ] :
    NullMeasurableSet s μ :=
  QuantumZipper.Thm18Asm.G4Core.coanalyticSet_nullMeasurableSet_of_sFinite hs μ

omit [PolishSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The image of an analytic set under a continuous map into a Polish space is
null-measurable. -/
theorem nullMeasurableSet_image_of_continuous {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} (hs : AnalyticSet s) (hf : Continuous f)
    (μ : Measure Y) [SFinite μ] : NullMeasurableSet (f '' s) μ :=
  analyticSet_nullMeasurableSet_of_sFinite (hs.image_of_continuous hf) μ

end Polish

section StandardBorel

variable {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α] [MeasurableSpace β]
  [StandardBorelSpace β]

/-- The image of a Borel set under a measurable map between standard Borel spaces is
null-measurable for every s-finite measure. -/
theorem nullMeasurableSet_image_of_measurable {f : α → β} {s : Set α} (hf : Measurable f)
    (hs : MeasurableSet s) (μ : Measure β) [SFinite μ] : NullMeasurableSet (f '' s) μ :=
  (LQGMetric.UMeasurableSet.image hf hs).nullMeasurableSet μ

/-- **"∃" over a standard Borel parameter.** For a Borel relation `S ⊆ α × β` between standard
Borel spaces, `{a | ∃ b, (a, b) ∈ S}` is null-measurable for every s-finite measure on `α`. -/
theorem nullMeasurableSet_setOf_exists {S : Set (α × β)} (hS : MeasurableSet S) (μ : Measure α)
    [SFinite μ] : NullMeasurableSet {a | ∃ b, (a, b) ∈ S} μ :=
  (LQGMetric.UMeasurableSet.setOf_exists hS).nullMeasurableSet μ

/-- **"∀" over a standard Borel parameter** (coanalytic). -/
theorem nullMeasurableSet_setOf_forall {S : Set (α × β)} (hS : MeasurableSet S) (μ : Measure α)
    [SFinite μ] : NullMeasurableSet {a | ∀ b, (a, b) ∈ S} μ :=
  (LQGMetric.UMeasurableSet.setOf_forall hS).nullMeasurableSet μ

/-- **"∃" events on a probability space.** If `Z : Ω → α` is an a.e.-measurable random variable
with values in a standard Borel space, and `S ⊆ α × β` is a Borel relation with a standard Borel
parameter space `β`, then the event `{ω | ∃ b, (Z ω, b) ∈ S}` is null-measurable. -/
theorem nullMeasurableSet_preimage_setOf_exists {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {Z : Ω → α} (hZ : AEMeasurable Z P) {S : Set (α × β)}
    (hS : MeasurableSet S) : NullMeasurableSet {ω | ∃ b, (Z ω, b) ∈ S} P :=
  (LQGMetric.UMeasurableSet.setOf_exists hS).nullMeasurableSet_preimage hZ

/-- **"∀" events on a probability space** (the complement form of
`nullMeasurableSet_preimage_setOf_exists`). -/
theorem nullMeasurableSet_preimage_setOf_forall {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {Z : Ω → α} (hZ : AEMeasurable Z P) {S : Set (α × β)}
    (hS : MeasurableSet S) : NullMeasurableSet {ω | ∀ b, (Z ω, b) ∈ S} P :=
  (LQGMetric.UMeasurableSet.setOf_forall hS).nullMeasurableSet_preimage hZ

end StandardBorel

end InteractingSLE
