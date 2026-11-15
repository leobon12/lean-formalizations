/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideLCLattice
import InteractingSLE.Spec.Sec7.SideLCGerm
import InteractingSLE.Spec.Sec7.PocketSideInInstGerm

/-!
# The native late collar leaf from per-`(s, q)` old-chart increment laws

PROVE-SIDE-LATCOL. `SideLCGerm.collar_of_oldChartIncrementLaws`, instantiated on every Ready late side test:
the collar binder `hSideCollar` (`LateSideCollar`) follows from

* `LateSideReferenceCharts`: countably many reference charts `old j r` with pair events `M j q r` inside the
  live event, conformal, containing the current relative chart's domain, with domain `H ∖ liveExt(refs.sets r)`;
* `LateSideIncrementLaws`: R.5's per-`(s, q)` law — for every version of the reference means and of the current
  mean, `HasOldChartIncrementLaw` between `old j r` and the relative chart at `q` on `M j q r`
  (the nested marked local-set law at the enlarged stop `T(q) ∨ s`, spec p. 475);
* `LateSideCover`: the pathwise selection at each access (an unfilled old half-disc in the current domain and
  the old-forward/current-inverse transition limit) together with the reference's own height, lift difference
  and the late word identity with the phase — clauses (C2)–(C4) of the collar;
* `hChart`: the base pocket chart is conformal on the target event (deterministic; `pChart_props`).

The germ comparison (C1) of the collar is proved (zero-boundary decay of the residual local set). The driven
property of the traversal is `SideTest.isDrivenCurve_target`. No Theorem 1.2/1.3 or `*_of_param` result is used.
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

/-- Every late side target carries the word frame's measure. -/
theorem SideTest.target_measure {Ω : Type} [MeasurableSpace Ω] (j : SideTest Ω) (i : BothLow)
    (d : WordObjects Ω) : (j.target i d).measure = d.measure := by
  rcases j with ⟨seed, outerEvent, event, chart, infinite, twoLeft⟩
  cases twoLeft <;> rfl

instance SideTest.isProbabilityMeasure_target {Ω : Type} [MeasurableSpace Ω] (j : SideTest Ω)
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure] :
    IsProbabilityMeasure (j.target i d).measure := by
  rw [SideTest.target_measure]
  infer_instance

/-- Reference charts and pair events of R.5 for every Ready late side test. -/
def LateSideReferenceCharts {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (old : SideTest Ω → ℕ → Ω → Chart)
    (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
    ∀ (q : ℝ≥0) (r : ℕ), ∀ ω ∈ M j q r, ω ∈ target.event ∧ (q : ℝ≥0∞) < capLife (target.curve ω) ∧
      (old j r ω).IsConformal ∧
      ((relChart target.baseChart target.curve q ω).dom : Set ℂ) ⊆ (old j r ω).dom ∧
      ((old j r ω).dom : Set ℂ) =
        H \ liveExt target.event target.curve target.domain (refs.sets r) refs.level ω

/-- R.5's per-`(s, q)` old-chart increment laws, for every version of the reference and current means. -/
def LateSideIncrementLaws {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω) (old : SideTest Ω → ℕ → Ω → Chart)
    (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
    ∀ (q : ℝ≥0) (gB : ℕ → Ω → DistOn upperHalfPlaneOpens),
    (∀ r, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets r) refs.level)
      target.zeroField target.measure (gB r)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((activeCompl target.event target.curve target.baseChart) q) target.zeroField
        target.measure g →
    ∀ r, HasOldChartIncrementLaw target.measure (M j q r) (old j r)
      (relChart target.baseChart target.curve q) (gB r) g

/-- The pathwise reference selection with the reference's own height, lift difference and the late word
identity (clauses (C2)–(C4) of the collar), at every access off the force jumps. -/
def LateSideCover {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (old : SideTest Ω → ℕ → Ω → Chart)
    (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω) : Prop :=
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

/-- **The late collar leaf with its germ clause proved.** On every Ready late side test, the collar binder
`hSideCollar` follows from the reference charts, R.5's per-`(s, q)` old-chart increment laws, and the
pathwise cover with the reference heights, lifts and word identity. -/
theorem lateSideCollar_of_incrementLaws {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (old : SideTest Ω → ℕ → Ω → Chart) (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω)
    (hChart : ∀ j : SideTest Ω, j.Ready d →
      ∀ ω ∈ (j.target i d).event, ((j.target i d).baseChart ω).IsConformal)
    (hRef : LateSideReferenceCharts i d side old M) (hLaw : LateSideIncrementLaws i d side old M)
    (hCov : LateSideCover i d side old M) : LateSideCollar i d side := by
  intro j hj _ _ _ _ q gB hgB g hg
  exact collar_of_oldChartIncrementLaws (M := M j q) (old := old j)
    (SideTest.isDrivenCurve_target hj) (hChart j hj) (hRef j hj q) (hLaw j hj q) (hCov j hj q)
    gB hgB g hg

end InteractingSLE.Wire
