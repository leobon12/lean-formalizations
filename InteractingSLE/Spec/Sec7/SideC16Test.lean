/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC5Slices

/-! # Testwise collars for the R90a branch partition

PROVE-SIDE-COLLAR2. This is exactly the existing collar clause, indexed
by a single test. No readiness condition or boundary coordinate is lost.
The global binder is equivalent to this clause for every ready test.
-/
set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 LocalSets Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketStopSide
  Sec7.Lemma71C Sec7.Aux119Heights

variable {Ω : Type} [MeasurableSpace Ω]

/-- The literal native collar at one capacity of one test. -/
def collarAtExc (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (e : Late.SideData Ω) (X : ℝ≥0 → Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  let target := j.target i d; let refs := e;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level)
      target.zeroField target.measure (gB i)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((activeCompl target.event target.curve target.baseChart) q) target.zeroField
        target.measure g →
    ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ v : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve target.baseChart) q ω) →
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (activeCompl target.event target.curve target.baseChart) q ω →
          g ω φ = ∫ z, v z * φ z) →
        ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω -
            segDriver (target.curve ω) q)
          (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω -
            segDriver (target.curve ω) q) →
          extendFrom H (relChart target.baseChart target.curve q ω).2.1 ξ ∉ X q ω →
          ∃ (i : ℕ) (b d : ℝ),
            let inv := (relChart target.baseChart target.curve q ω).2.1;
            let vB := harmRep (gB i ω)
              (H \ liveExt target.event target.curve target.domain (refs.sets i) refs.level ω);
            Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
            Tendsto (fun y => vB (inv y) + target.harmonic (inv y) +
                chiC target.kappa * refs.lift i ω (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
            Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2 (inv y) -
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

/-- The full collar at every capacity of one test. -/
def collarExc (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (e : Late.SideData Ω) (X : ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ q : ℝ≥0, j.collarAtExc i d e X q

/-- Assemble the initial collar and every positive-capacity collar. -/
theorem collarExc_of_pos_zero {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    {e : Late.SideData Ω} {X : ℝ≥0 → Ω → Set ℂ}
    (hpos : ∀ q : ℝ≥0, 0 < q → j.collarAtExc i d e X q)
    (hzero : j.collarAtExc i d e (fun _ _ => ∅) 0) : j.collarExc i d e X := by
  intro q
  by_cases hq : q = 0
  · subst q
    intro gB hgB g hg
    filter_upwards [hzero gB hgB g hg] with ω hω hA hlive v hv hrep ξ hξ _
    exact hω hA hlive v hv hrep ξ hξ (Set.notMem_empty _)
  · exact hpos q (lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ q) (Ne.symm hq))

end InteractingSLE.Wire.Current.SideTest

namespace InteractingSLE.Wire

open Current

/-- Testwise indexing leaves the existing fixed-capacity binder unchanged. -/
theorem lateSideCollarAtExc_iff_testwise {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (q : ℝ≥0) :
    LateSideCollarAtExc i d side X q ↔
      ∀ j : SideTest Ω, j.Ready d → j.collarAtExc i d (side j) (X j) q := Iff.rfl

/-- The existing assembly binder requires all unrefined ready tests.
R90a instead uses the same testwise clause on each retained branch fibre. -/
theorem lateSideCollarExc_iff_testwise {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) :
    LateSideCollarExc i d side X ↔
      ∀ j : SideTest Ω, j.Ready d → j.collarExc i d (side j) (X j) := Iff.rfl

end InteractingSLE.Wire
