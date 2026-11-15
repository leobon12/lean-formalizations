/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC18Top

/-! # The tops' test-first collar with an explicit current chart

PROVE-SIDE-COLLAR2. This is the existing tops' collar clause with the
current chart supplied as an argument. Its R100 specialization relifts
the current chart and every reference chart by the same integer.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC19
open Wire Wire.Current LocalSets PocketStop PocketTraversal PocketStopSide Lemma71C Aux119Heights

/-- The tops' literal collar, test first, with every occurrence of the
current chart exposed. References, means, word and exceptional set retain
their original meaning. -/
def LateSideCollarExcWithChart {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (current : SideTest Ω → Ω → Chart)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0,
    ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level)
      target.zeroField target.measure (gB i)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((activeCompl target.event target.curve (current j)) q) target.zeroField
        target.measure g →
    ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ v : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve (current j)) q ω) →
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (activeCompl target.event target.curve (current j)) q ω →
          g ω φ = ∫ z, v z * φ z) →
        ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω -
            segDriver (target.curve ω) q)
          (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω -
            segDriver (target.curve ω) q) →
          extendFrom H (relChart (current j) target.curve q ω).2.1 ξ ∉ X j q ω →
          ∃ (i : ℕ) (b d : ℝ),
            let inv := (relChart (current j) target.curve q ω).2.1;
            let vB := harmRep (gB i ω)
              (H \ liveExt target.event target.curve target.domain (refs.sets i) refs.level ω);
            Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
            Tendsto (fun y => vB (inv y) + target.harmonic (inv y) +
                chiC target.kappa * refs.lift i ω (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
            Tendsto (fun y => (relChart (current j) target.curve q ω).2.2 (inv y) -
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

/-- This explicit-chart binder specializes to the original tops' binder. -/
theorem lateSideCollarExcWithChart_principal_iff {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) :
    LateSideCollarExcWithChart i d side (fun j => (j.target i d).baseChart) X ↔
      LateSideCollarExc i d side X := Iff.rfl

/-- The test-first clause is exactly C18's fixed-test clause. -/
theorem lateSideCollarExcWithChart_iff_testwise {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (current : SideTest Ω → Ω → Chart) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) :
    LateSideCollarExcWithChart i d side current X ↔
      ∀ j, j.Ready d → ∀ q, SideC18.collarAtExcWithChart j i d (side j) (current j) (X j) q := Iff.rfl

/-- Reorder C18's capacity-first result into the tops' test-first binder;
the current chart is relifted with the same integer as the references. -/
theorem lateSideCollarExcWithChart_shift_iff {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (m : SideTest Ω → Ω → ℤ) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) :
    LateSideCollarExcWithChart i d side
      (fun j ω => PocketStopField.shiftChart ((j.target i d).baseChart ω) (m j ω)) X ↔
      SideC18.LateSideCollarExcShift i d side m X := by
  constructor
  · intro h q j hj
    exact h j hj q
  · intro h j hj
    exact fun q => h q j hj

end InteractingSLE.Sec7.SideC19
