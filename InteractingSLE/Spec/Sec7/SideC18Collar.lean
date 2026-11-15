/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC18Data
import InteractingSLE.Spec.Sec7.SideC16Test

/-! # The collar with its current chart explicit

PROVE-SIDE-COLLAR2. R100 relifts the current chart as well as every
reference chart. The principal specialization is the existing collar.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Sec7.SideC18
open Wire Wire.Current LocalSets PocketStop PocketTraversal PocketStopSide Lemma71C Aux119Heights

/-- The exact fixed-test collar with the chosen current chart exposed. -/
def collarAtExcWithChart {Ω : Type} [MeasurableSpace Ω] (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (e : Late.SideData Ω) (c : Ω → Chart) (X : ℝ≥0 → Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  let target := j.target i d; let refs := e;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level)
      target.zeroField target.measure (gB i)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((activeCompl target.event target.curve c) q) target.zeroField
        target.measure g →
    ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ v : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve c) q ω) →
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (activeCompl target.event target.curve c) q ω →
          g ω φ = ∫ z, v z * φ z) →
        ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω -
            segDriver (target.curve ω) q)
          (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω -
            segDriver (target.curve ω) q) →
          extendFrom H (relChart c target.curve q ω).2.1 ξ ∉ X q ω →
          ∃ (i : ℕ) (b d : ℝ),
            let inv := (relChart c target.curve q ω).2.1;
            let vB := harmRep (gB i ω)
              (H \ liveExt target.event target.curve target.domain (refs.sets i) refs.level ω);
            Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
            Tendsto (fun y => vB (inv y) + target.harmonic (inv y) +
                chiC target.kappa * refs.lift i ω (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
            Tendsto (fun y => (relChart c target.curve q ω).2.2 (inv y) -
                refs.lift i ω (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
            b + chiC target.kappa * d = forceBoundaryData target.kappa target.rhoL target.rhoR
              (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω -
                segDriver (target.curve ω) q)
              (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω -
                segDriver (target.curve ω) q)
              ξ + refs.phase q ω * (Ioo
                (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL
                  zL q ω - segDriver (target.curve ω) q)
                (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR
                  zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - refs.offset

/-- The principal specialization is the landed fixed-test predicate. -/
theorem collarAtExcWithChart_principal_iff {Ω : Type} [MeasurableSpace Ω]
    (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) (e : Late.SideData Ω)
    (X : ℝ≥0 → Ω → Set ℂ) (q : ℝ≥0) :
    collarAtExcWithChart j i d e (j.target i d).baseChart X q ↔ j.collarAtExc i d e X q := Iff.rfl

/-- The complete fixed-capacity collar in the R100 chart. -/
def LateSideCollarAtExcShift {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (m : SideTest Ω → Ω → ℤ)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → collarAtExcWithChart j i d (side j)
    (fun ω => PocketStopField.shiftChart ((j.target i d).baseChart ω) (m j ω)) (X j) q

/-- The R100 collar at all relative capacities. -/
def LateSideCollarExcShift {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (m : SideTest Ω → Ω → ℤ)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ q : ℝ≥0, LateSideCollarAtExcShift i d side m X q

end InteractingSLE.Sec7.SideC18
