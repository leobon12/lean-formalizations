/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorSide
import InteractingSLE.Spec.Sec7.Aux29CorChart
import InteractingSLE.Spec.Wire.Thm12LateSide

/-!
# Theorem 1.2's late R.7 side limits with the collar off the tip and the outgoing corner

PROVE-AUX29-CORNER. `late_sideLimits_offExc` is `Wire.late_sideLimits` (the native all-`q` side limit
of one late side test, consumed by `late_pocketSideInput`) with the collar leaf weakened to the
source's Lemma R.5: the comparison is needed only at real current coordinates whose physical landing
avoids a finite set `X q ω` (the current tip and the bounded pocket's outgoing corner). Aux. 29 covers
all prime ends over those points (`Aux29Cor.pocketStopPhaseSideLimit_of_collar_offExc`). The base
chart's facts come from `SideTest.Ready` (`SideTest.baseChart_aux29Facts`).

Conditional helper with a distinct name; `late_sideLimits` and its consumers are unchanged. Nothing
here uses Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal
namespace InteractingSLE.Wire
open Current Sec7 LocalSets WangWu WholeField Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt Sec7.Aux119Heights Sec7.PhaseSel

/-- **`late_sideLimits` with the R.5 collar required only off a finite exceptional physical set**
(PROVE-AUX29-CORNER). The same conclusion as `Wire.late_sideLimits` (the native all-`q` side limit of
one late side test), where the collar leaf `hCollar` is replaced by `hCollarExc`: R.5's comparison is
asked only at real current coordinates `ξ` whose physical landing `extendFrom H inv ξ` avoids the
finite set `X q ω` (for R.7: the current tip and the bounded pocket's outgoing corner, where R.5 gives
no comparison, spec pp. 474–475). The prime ends over `X q ω` are covered by Aux. 29
(`Aux29Cor.pocketStopPhaseSideLimit_of_collar_offExc`). New inputs: `hj` (the test is `Ready`;
it supplies the base chart's lift, boundary extension and landing at `∞`), `hKm` (hitting
measurability of the active complement), `hu`, `hub` (the deterministic mean is bounded harmonic). -/
theorem late_sideLimits_offExc {Ω : Type} [mΩ : MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (j : SideTest Ω) (e : Late.SideData Ω)
    (hDriven : ∀ ω ∈ (j.target i d).event, IsDrivenCurve ((j.target i d).curve ω))
    (hOpen : ∀ ω ∈ (j.target i d).event, IsOpen ((j.target i d).domain ω))
    (hZero : IsZeroBoundaryGFF upperHalfPlaneOpens (j.target i d).zeroField (j.target i d).measure)
    (hpre : let target := j.target i d;
      ∀ i, locPrefixSigma (e.info i) target.event target.curve e.level ≤ mΩ)
    (hFo : let target := j.target i d; ∀ i ω, ω ∈ target.event → IsOpen (H \ e.sets i ω))
    (hRawReference : let target := j.target i d; ∀ i, PocketStopUnionLaw (e.info i) target.measure
      target.event target.curve target.domain (e.sets i) target.zeroField e.level)
    (hLattice : let target := j.target i d; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      (q : ℝ≥0∞) < capLife (target.curve ω) → ∃ m : ℤ, e.phase q ω = m * phaseStep target.kappa)
    (hj : j.Ready d)
    (hKm : ∀ q : ℝ≥0, Measurable[mΩ, hittingSigma]
      (activeCompl (j.target i d).event (j.target i d).curve (j.target i d).baseChart q))
    (hu : InnerProductSpace.HarmonicOnNhd (j.target i d).harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |(j.target i d).harmonic z| ≤ M)
    (X : ℝ≥0 → Ω → Set ℂ) (hX : ∀ q ω, (X q ω).Finite)
    (hCollarExc : let target := j.target i d; let zL := Late.leftZero i d j;
      let zR := Late.rightZero i d j; ∀ q : ℝ≥0, ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (e.sets i) e.level)
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
                (H \ liveExt target.event target.curve target.domain (e.sets i) e.level ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + target.harmonic (inv y) +
                  chiC target.kappa * e.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2 (inv y) - e.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + chiC target.kappa * d = forceBoundaryData target.kappa target.rhoL target.rhoR
                (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω -
                  segDriver (target.curve ω) q)
                (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω -
                  segDriver (target.curve ω) q)
                ξ + e.phase q ω * (Ioo
                  (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL
                    zL q ω - segDriver (target.curve ω) q)
                  (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR
                    zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - e.offset)
    (hProbes : let target := j.target i d; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (e.probe N ω) S ∧ ContinuousOn (e.baseProbe N ω) S ∧ ContinuousOn (e.weight N ω) S ∧
        ∀ t ∈ S, 0 < e.weight N ω t ∧ e.probe N ω t - e.baseProbe N ω t = e.phase t ω * e.weight N ω t)
    (hJointGerms : let target := j.target i d; ∀ i, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      ω ∈ e.event i →
      ∃ (ξ η y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU b : ℝ),
        IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
        (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
        ContinuousOn (fun y : ℝ => L y) J ∧
        (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
        bC = bU ∧ bU = bC + chiC target.kappa * (L y₀).im ∧
        ContinuousWithinAt L Hbar (ξ : ℂ) ∧
        Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)) ∧
        Tendsto (e.currentMean i ω) (𝓝[H] (ξ : ℂ)) (𝓝 (b + e.phase (e.visit i ω) ω)) ∧
        Tendsto (e.referenceMean i ω) (𝓝[H] (η : ℂ)) (𝓝 b) ∧
        Tendsto (fun z => e.referenceMean i ω (φ z) - e.currentMean i ω z -
            chiC target.kappa * (L z).im)
          (𝓝[H] (ξ : ℂ)) (𝓝 0))
    (hVisits : let target := j.target i d; ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      0 < capLife (target.curve ω) →
      ∃ i, 0 < e.visit i ω ∧ (e.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ e.event i)
    : ∃ (n : Ω → ℤ) (a : ℝ), Measurable[(j.target i d).walls] n ∧
      ∀ q : ℝ≥0, (j.target i d).Limit n a q := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  have hκ : 4 < 16 / (16 / i.kappa) := by rw [hdual]; exact i.kappa_gt_four
  have hκ0 : 0 < 16 / (16 / i.kappa) := by linarith
  have hbase := fun ω (hω : ω ∈ (j.target i d).event) => SideTest.baseChart_aux29Facts (i := i) hj hω
  refine ⟨fun _ => 0, e.offset, measurable_const, ?_⟩
  intro q
  rcases j with ⟨seed, outer, event, chart, infinite, twoLeft⟩
  cases twoLeft
  · have hs := pocketStopSideLimit_of_phase_probes_joint_germs
      (P := d.measure) (ρL := wordL1 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight))
      (ρR := wordR2 (16 / i.kappa) (rs136Theta2 (16 / i.kappa) i.rightWeight))
      (xL := marksL1All) (xR := marksRAll (d.leftWall seed) (StripSys.rt seed) chart)
      (K := fun s => activeCompl event
        (if infinite then travAllInf d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart
          else travAll d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart)
        (pChart event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed))
          chart) s)
      (c := pChart event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed))
        chart)
      (a := e.offset) (δ := e.phase)
      hκ hDriven (fun ω _ => by rfl) (fun ω _ => by rfl)
      (fun q => Aux29Cor.pocketStopPhaseSideLimit_of_collar_offExc hκ0 hZero hpre hOpen hFo
        hRawReference (hLattice q) hDriven (fun ω hω => (hbase ω hω).1)
        (fun ω hω => (hbase ω hω).2.1)
        (fun ω hω => (hbase ω hω).2.2) (hKm q) hu hub (hX q) (hCollarExc q))
      hProbes hJointGerms hVisits
    convert hs q using 1
    simp [SideTarget.Limit, SideTest.target, SideTarget.baseChart, PocketStopField.shiftChart]
  · have hs := pocketStopSideLimit_of_phase_probes_joint_germs
      (P := d.measure) (ρL := wordL2 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight))
      (ρR := wordR2 (16 / i.kappa) (rs136Theta2 (16 / i.kappa) i.rightWeight))
      (xL := marksL2All d.rightWall chart)
      (xR := marksRAll (d.leftWall seed) (StripSys.rt seed) chart)
      (K := fun s => activeCompl event
        (if infinite then travAllInf d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart
          else travAll d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart)
        (pChart event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed))
          chart) s)
      (c := pChart event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed))
        chart)
      (a := e.offset) (δ := e.phase)
      hκ hDriven (fun ω _ => by rfl) (fun ω _ => by rfl)
      (fun q => Aux29Cor.pocketStopPhaseSideLimit_of_collar_offExc hκ0 hZero hpre hOpen hFo
        hRawReference (hLattice q) hDriven (fun ω hω => (hbase ω hω).1)
        (fun ω hω => (hbase ω hω).2.1)
        (fun ω hω => (hbase ω hω).2.2) (hKm q) hu hub (hX q) (hCollarExc q))
      hProbes hJointGerms hVisits
    convert hs q using 1
    simp [SideTarget.Limit, SideTest.target, SideTarget.baseChart, PocketStopField.shiftChart]

end InteractingSLE.Wire
