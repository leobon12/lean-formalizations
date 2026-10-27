import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import MatedCRTHarmonic.GMS4b.Lemma47
import MatedCRTHarmonic.LQGCone.AreaBridge
import MatedCRTHarmonic.CellScaling.ConeDefs
import LQGMetric.Field.CircleAvgBridge
import LQGMetric.Papers.DFGPS.L2_3Tail

/-!
# Model-specific inputs for [18] Lemma 4.7

The event in `UpperMassBoundModel` uses the dyadic LQG area of the actual
`γ`-quantum-cone field in the frozen mating-of-trees coupling. The event in
`CircleAverageSupBoundModel` uses a jointly continuous version of the circle
averages of a normalized whole-plane GFF. These definitions record the
distributional data absent from the abstract G4b interfaces.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCUpper

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.GMSLemma27

/-- The LQG area of the frozen bundle's `γ`-quantum-cone field. -/
def gammaConeArea {Ω : Type} [MeasurableSpace Ω] (γ : ℝ)
    (X : Ω → Field) (B B' : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℂ :=
  CellScaling.lqgArea γ
    (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))

/-- The canonical GMC measure of a normalized whole-plane GFF. -/
def wholePlaneArea {Ω : Type} [MeasurableSpace Ω] (γ : ℝ)
    (Y : Ω → LQGMetric.DistC) (ω : Ω) : Measure ℂ :=
  CellScaling.lqgArea γ (Y ω)

/-- The area of the frozen coupling's 0-quantum cone, with its own radial
Brownian motions and no free area measure. -/
def zeroConeArea {Ω : Type} [MeasurableSpace Ω] (γ : ℝ)
    (X₀ : Ω → Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℂ :=
  CellScaling.lqgArea γ
    (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))

/-- The upper-mass event for the actual normalized whole-plane GMC area. -/
def UpperMassBoundWholePlaneModel {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → LQGMetric.DistC} {γ : ℝ}
    (_hγ : γ ∈ Ioo (0 : ℝ) 2)
    (_hY : LQGMetric.IsNormalizedWPGFF Y P) : Prop :=
  ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Y ω (ball z δ)} ≤
      ENNReal.ofReal (C * δ ^ β)

/-- The upper-mass event for the frozen coupling's actual 0-cone GMC area. -/
def UpperMassBoundZeroConeModel {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (_hγ : γ ∈ Ioo (0 : ℝ) 2)
    (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Prop :=
  ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (δ ^ ξ) < zeroConeArea γ X₀ B₀ B₀' ω (ball z δ)} ≤
      ENNReal.ofReal (C * δ ^ β)

/-- The frozen cone's area is the canonical area of the ported GMC
construction, with no alternative measure or off-curve atoms. -/
theorem gammaConeArea_eq_qAreaC {Ω : Type} [MeasurableSpace Ω]
    (γ : ℝ) (X : Ω → Field) (B B' : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    gammaConeArea γ X B B' ω =
      MoTPort.qAreaC γ
        (coneField (X ω) (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) := by
  unfold gammaConeArea
  exact LQGCone.lqgArea_eq_qAreaC γ _

/-- The upper small-ball mass estimate for the actual `γ`-cone area.
Unlike the abstract `GMS4b.UpperMassBound`, the area is fixed by the field
and radial Brownian motions of the frozen coupling. -/
def UpperMassBoundModel {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (_hγ : γ ∈ Ioo (0 : ℝ) 2)
    (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Prop :=
  ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (δ ^ ξ) < gammaConeArea γ X B B' ω (ball z δ)} ≤
      ENNReal.ofReal (C * δ ^ β)

/-- The sharp supremum estimate for a jointly continuous version of the
circle averages of a normalized whole-plane GFF. -/
def CircleAverageSupBoundModel {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → LQGMetric.DistC)
    (H : ℝ → ℂ → Ω → ℝ)
    (_hX : LQGMetric.IsNormalizedWPGFF X P)
    (_hH : LQGMetric.DFGPS.IsCircleAvgVersion X P H) : Prop :=
  GMS4b.CircleAverageSupBound P H

/-- Every normalized whole-plane GFF has a jointly continuous circle-average
version satisfying the pinned Gaussian covariance interface. -/
theorem exists_circleAvgVersion_normalized {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → LQGMetric.DistC}
    (hX : LQGMetric.IsNormalizedWPGFF X P) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      LQGMetric.DFGPS.IsCircleAvgVersion X P H ∧
        LQGDimension.IsGFFCircleAverage H P := by
  obtain ⟨H, hG, hcont, hae⟩ :=
    LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized hX
  exact ⟨H, ⟨hcont, hae⟩, hG⟩

/-- The model estimate supplies G4b's abstract input when the cell model's
area is definitionally identified with the cone area. -/
theorem upperMassBound_of_model {γ : ℝ} (M : CellModel γ)
    {X X₀ hIG₀ : M.Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → M.Ω → ℝ} {U : M.Ω → ℝ}
    {ηL η η₀ : M.Ω → C(ℝ, ℂ)} {bm : M.Ω → Path2}
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (D : IsMatingOfTreesCoupling γ M.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (harea : ∀ ω : M.Ω, M.area ω = gammaConeArea γ X B B' ω)
    (hmass : UpperMassBoundModel hγ D) : GMS4b.UpperMassBound M := by
  rcases hmass with ⟨ξ, β, hξ, hβ, hb⟩
  refine ⟨ξ, β, hξ, hβ, ?_⟩
  intro ρ hρ
  obtain ⟨C, hC⟩ := hb ρ hρ
  refine ⟨C, fun δ hδ => ?_⟩
  simpa only [GMS4b.UpperMassBound, harea] using hC δ hδ

/-- The normalized GFF model estimate is exactly the circle-average input
consumed by G4b. -/
theorem circleAverageSupBound_of_model {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → LQGMetric.DistC}
    {H : ℝ → ℂ → Ω → ℝ}
    (hX : LQGMetric.IsNormalizedWPGFF X P)
    (hH : LQGMetric.DFGPS.IsCircleAvgVersion X P H)
    (hbound : CircleAverageSupBoundModel P X H hX hH) :
    GMS4b.CircleAverageSupBound P H := hbound

/-- Apply G4b's Lemma 4.7 to the `γ`-cone cell model after identifying
its area with the dyadic LQG area of the frozen bundle's cone field. -/
theorem lemma47_of_gammaConeModel {γ : ℝ} (M : CellModel γ)
    {X X₀ hIG₀ : M.Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → M.Ω → ℝ} {U : M.Ω → ℝ}
    {ηL η η₀ : M.Ω → C(ℝ, ℂ)} {bm : M.Ω → Path2}
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (D : IsMatingOfTreesCoupling γ M.P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (harea : ∀ ω : M.Ω, M.area ω = gammaConeArea γ X B B' ω)
    (hSLE : SegmentsContainBalls M) (hGMC : GMCLowerTail γ)
    (hdom : AreaDominatesWholePlaneGFF M)
    (hmass : UpperMassBoundModel hγ D)
    (hgeom : GMS4b.SpaceFillingGeometry M) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ ζ ∈ Ioo (0 : ℝ) 1,
      ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
        M.P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
          ENNReal.ofReal (ε ^ (-ζ)) < ((GMS4b.degreeOut ε (M.curve ω) z : ℕ∞) : ℝ≥0∞)} ≤
          ENNReal.ofReal (C * ε ^ α) := by
  exact GMS4b.lemma47_holds M hγ.1 hSLE hGMC hdom
    (upperMassBound_of_model M hγ D harea hmass) hgeom

end MatedCRTHarmonic.GMCUpper
