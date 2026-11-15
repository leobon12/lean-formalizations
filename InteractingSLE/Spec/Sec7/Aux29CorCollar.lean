/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideLCLate
import InteractingSLE.Spec.Sec7.Aux29CorChart

/-!
# Theorem 1.2's late R.7 collar leaf off the tip and the outgoing corner

PROVE-AUX29-CORNER. PROVE-SIDE-LATCOL reduced the late collar leaf `LateSideCollar` (the `hSideCollar`
binder of `late_pocketSideInput`) to reference charts, R.5's per-capacity increment laws and a pathwise
cover (`lateSideCollar_of_incrementLaws`). Both the binder and the cover ask for R.5's comparison at
**every** real current coordinate off the jump set, including those whose physical landing is the
current tip or the bounded pocket's outgoing corner, where R.5 gives none (spec pp. 474–475). This file:

* `LateSideCollarExc i d side X`: the collar binder asked only where the physical landing
  `extendFrom H inv ξ` avoids `X j q ω` (a finite exceptional physical set per test and capacity);
  `lateSideCollarExc_of_lateSideCollar`: it is weaker than `LateSideCollar`;
* `LateSideCoverExc`: LATCOL's cover with the same restriction;
  **`lateSideCollarExc_of_incrementLaws`**: references, increment laws and the restricted cover give the
  restricted collar, with the base-chart conformality discharged from `Ready`;
* `lateSideCollar_of_incrementLaws_ready`: LATCOL's reduction with its deterministic input `hChart`
  discharged (`SideTest.isConformal_baseChart_of_ready`).

`late_sideLimits_offExc` (`Aux29CorLate`) consumes `LateSideCollarExc` per test (Aux. 29 covers the
excluded prime ends).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStopField Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketAdapt
  Sec7.Lemma71C Sec7.PocketStopSide Sec7.Aux119Heights Sec7.PhaseSel

/-- **The late collar binder off a finite exceptional physical set** `X j q ω`: `LateSideCollar` with
the comparison asked only at coordinates whose physical landing avoids `X j q ω`. -/
def LateSideCollarExc {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0,
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
          extendFrom H (relChart target.baseChart target.curve q ω).2.1 ξ ∉ X j q ω →
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

/-- The restricted collar is weaker than LATCOL's collar. -/
theorem lateSideCollarExc_of_lateSideCollar {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hC : LateSideCollar i d side) : LateSideCollarExc i d side X := by
  intro j hj _ _ _ _ q gB hgB g hg
  filter_upwards [hC j hj q gB hgB g hg] with ω hω hA hq v hv hvr ξ hξ _
  exact hω hA hq v hv hvr ξ hξ

/-- **LATCOL's pathwise cover off a finite exceptional physical set** `X j q ω`. -/
def LateSideCoverExc {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (old : SideTest Ω → ℕ → Ω → Chart)
    (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ (q : ℝ≥0) (gB : ℕ → Ω → DistOn upperHalfPlaneOpens),
    (∀ r, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets r) refs.level)
      target.zeroField target.measure (gB r)) →
    ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω -
            segDriver (target.curve ω) q)
          (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω -
            segDriver (target.curve ω) q) →
        extendFrom H (relChart target.baseChart target.curve q ω).2.1 ξ ∉ X j q ω →
        ∃ (r : ℕ) (x ε b d : ℝ), ω ∈ M j q r ∧ 0 < ε ∧
          (old j r ω).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (relChart target.baseChart target.curve q ω).dom ∧
          Tendsto (fun z => (old j r ω).1 ((relChart target.baseChart target.curve q ω).2.1 z))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (fun y => harmRep (gB r ω)
                (H \ liveExt target.event target.curve target.domain (refs.sets r) refs.level ω)
                ((relChart target.baseChart target.curve q ω).2.1 y) +
              target.harmonic ((relChart target.baseChart target.curve q ω).2.1 y) +
              chiC target.kappa * refs.lift r ω ((relChart target.baseChart target.curve q ω).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
          Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2
                ((relChart target.baseChart target.curve q ω).2.1 y) -
              refs.lift r ω ((relChart target.baseChart target.curve q ω).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
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

/-- **The restricted late collar from R.5's increment laws** (PROVE-SIDE-LATCOL's reduction with the
cover asked only off the exceptional physical set; the base-chart conformality from `Ready`). -/
theorem lateSideCollarExc_of_incrementLaws {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (old : SideTest Ω → ℕ → Ω → Chart) (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRef : LateSideReferenceCharts i d side old M) (hLaw : LateSideIncrementLaws i d side old M)
    (hCov : LateSideCoverExc i d side old M X) : LateSideCollarExc i d side X := by
  intro j hj _ _ _ _ q gB hgB g hg
  refine (collar_of_oldChartIncrementLaws (M := M j q) (old := old j)
    (J := fun ω => forceJumpSet
      (fun l => geomLW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksL l q ω -
        segDriver ((j.target i d).curve ω) q)
      (fun k => geomRW (fun t ω => segDriver ((j.target i d).curve ω) t) (j.target i d).marksR k q ω -
        segDriver ((j.target i d).curve ω) q) ∪
      {ξ : ℝ | extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 ξ ∈ X j q ω})
    (SideTest.isDrivenCurve_target hj) (fun ω _ => SideTest.isConformal_baseChart_of_ready hj ω)
    (hRef j hj q) (hLaw j hj q) (fun gB hgB => ?_) gB hgB g hg).mono
    fun ω hω hA hq v hv hvr ξ hξ hξX => hω hA hq v hv hvr ξ fun h => h.elim hξ hξX
  filter_upwards [hCov j hj q gB hgB] with ω hω hA hq ξ hξ
  exact hω hA hq ξ (fun h => hξ (Or.inl h)) (fun h => hξ (Or.inr h))

/-- PROVE-SIDE-LATCOL's `lateSideCollar_of_incrementLaws` with its deterministic input `hChart`
(base-chart conformality) discharged from `Ready`. -/
theorem lateSideCollar_of_incrementLaws_ready {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (old : SideTest Ω → ℕ → Ω → Chart) (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω)
    (hRef : LateSideReferenceCharts i d side old M) (hLaw : LateSideIncrementLaws i d side old M)
    (hCov : LateSideCover i d side old M) : LateSideCollar i d side :=
  lateSideCollar_of_incrementLaws i d side old M
    (fun _ hj ω _ => SideTest.isConformal_baseChart_of_ready hj ω) hRef hLaw hCov

end InteractingSLE.Wire
