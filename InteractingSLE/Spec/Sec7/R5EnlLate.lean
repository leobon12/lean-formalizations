/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorCollar
import InteractingSLE.Spec.Sec7.R5EnlCollar

/-!
# The late side collar from the conditioned increment laws

Packet PROVE-R5-ENLARGED. PROVE-SIDE-COLLAR2's remaining `hLaw : LateSideIncrementLaws …` asks for the unconditioned
`HasOldChartIncrementLaw` on the late side tests. As on the R.7 tests (`R5EnlCond.lean`), the late normalized reference
`liveExt target.event target.curve target.domain (refs.sets r) refs.level` is all of `ℍ` off the candidate event, so
the reference residual is a zero-boundary GFF only conditionally on the reference event. Here:

* `LateSideIncrementLawsOn` — the late increment laws in the conditioned form;
* `lateSideIncrementLawsOn_of_lateSideIncrementLaws` — the old form implies it;
* **`lateSideCollarExc_of_incrementLawsOn`** — PROVE-AUX29-CORNER's `lateSideCollarExc_of_incrementLaws` with the
  conditioned laws: references + conditioned laws + the cover off `X` give `LateSideCollarExc`.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStopField Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketAdapt
  Sec7.Lemma71C Sec7.PocketStopSide Sec7.Aux119Heights Sec7.PhaseSel Sec7.R5Enl

/-- **R.5's per-`(s, q)` late increment laws, conditioned on the reference event**, for every version of the
reference and current means (`LateSideIncrementLaws` with `HasOldChartIncrementLawOn`). -/
def LateSideIncrementLawsOn {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω) (old : SideTest Ω → ℕ → Ω → Chart)
    (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j;
    ∀ (q : ℝ≥0) (gB : ℕ → Ω → DistOn upperHalfPlaneOpens),
    (∀ r, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets r) refs.level)
      target.zeroField target.measure (gB r)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean ((activeCompl target.event target.curve target.baseChart) q) target.zeroField
        target.measure g →
    ∀ r, HasOldChartIncrementLawOn target.measure (M j q r) (old j r)
      (relChart target.baseChart target.curve q) (gB r) g

/-- The unconditioned late laws imply the conditioned ones. -/
theorem lateSideIncrementLawsOn_of_lateSideIncrementLaws {Ω : Type} [MeasurableSpace Ω] {i : BothLow}
    {d : WordObjects Ω} [IsProbabilityMeasure d.measure] {side : SideTest Ω → Late.SideData Ω}
    {old : SideTest Ω → ℕ → Ω → Chart} {M : SideTest Ω → ℝ≥0 → ℕ → Set Ω}
    (h : LateSideIncrementLaws i d side old M) : LateSideIncrementLawsOn i d side old M :=
  fun j hj q gB hgB g hg r => hasOldChartIncrementLawOn_of_hasOldChartIncrementLaw (h j hj q gB hgB g hg r)

/-- **The restricted late collar from R.5's conditioned increment laws** (`lateSideCollarExc_of_incrementLaws`
with `LateSideIncrementLawsOn`). -/
theorem lateSideCollarExc_of_incrementLawsOn {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (old : SideTest Ω → ℕ → Ω → Chart) (M : SideTest Ω → ℝ≥0 → ℕ → Set Ω)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRef : LateSideReferenceCharts i d side old M) (hLaw : LateSideIncrementLawsOn i d side old M)
    (hCov : LateSideCoverExc i d side old M X) : LateSideCollarExc i d side X := by
  intro j hj _ _ _ _ q gB hgB g hg
  refine (collar_of_oldChartIncrementLawsOn (M := M j q) (old := old j)
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

end InteractingSLE.Wire
