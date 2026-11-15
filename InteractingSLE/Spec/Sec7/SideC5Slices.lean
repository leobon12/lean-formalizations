/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorCollar

/-!
# Fixed-capacity collars and their initial slice

PROVE-SIDE-COLLAR2 continuation. Actual old interior visits can be used
only at positive current capacity. Separate the fixed-capacity binder so
that this restriction is explicit. The full native collar follows after
its initial slice is also supplied; no positive visit is asserted at zero.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStopField Sec7.PocketStop Sec7.PocketTraversal
  Sec7.PocketAdapt Sec7.Lemma71C Sec7.PocketStopSide Sec7.Aux119Heights Sec7.PhaseSel

/-- The exact native collar clause at one specified relative capacity. -/
def LateSideCollarAtExc {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
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

/-- The exact pathwise reference cover at one specified capacity. -/
def LateSideCoverAtExc {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (old : SideTest Ω → ℕ → Ω → Chart)
    (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
    let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
    ∀ (gB : ℕ → Ω → DistOn upperHalfPlaneOpens),
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

/-- The existing R.5 reduction at a fixed relative capacity. -/
theorem lateSideCollarAtExc_of_incrementLaws {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (old : SideTest Ω → ℕ → Ω → Chart) (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRef : LateSideReferenceCharts i d side old M) (hLaw : LateSideIncrementLaws i d side old M)
    (q : ℝ≥0) (hCov : LateSideCoverAtExc i d side old M X q) :
    LateSideCollarAtExc i d side X q := by
  intro j hj _ _ _ _ gB hgB g hg
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
  filter_upwards [hCov j hj gB hgB] with ω hω hA hq ξ hξ
  exact hω hA hq ξ (fun h => hξ (Or.inl h)) (fun h => hξ (Or.inr h))

/-- Positive-capacity collars and the separate initial clause give exactly
Aux29's native collar off exceptional physical fibres. -/
theorem lateSideCollarExc_of_pos_and_zero {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hPos : ∀ q : ℝ≥0, 0 < q → LateSideCollarAtExc i d side X q)
    (hZero : LateSideCollarAtExc i d side X 0) :
    LateSideCollarExc i d side X := by
  intro j hj _ _ _ _ q gB hgB g hg
  by_cases hq : q = 0
  · subst q
    exact hZero j hj gB hgB g hg
  · exact hPos q (pos_iff_ne_zero.2 hq) j hj gB hgB g hg

end InteractingSLE.Wire
