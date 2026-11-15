/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorLate
import InteractingSLE.Spec.Sec7.SideC18Collar

/-! # Late R.7 side limits from the collar in R100's relifted current chart

PROVE-T12-ASSEMBLE5. PROVE-SIDE-COLLAR2 proved the complete late collar in ruling R100's normalization
(`SideC18.sideCollarInputExcShift_holds`): the current chart is the base chart relifted by a walls-measurable integer
`m` (`PocketStopField.shiftChart`, lift `− 2πm`), the references are relifted by the same `m`, the offset is `0`.
The old consumer `Wire.late_sideLimits_offExc` reads the collar in the principal base chart and concludes the native
side limit `SideTarget.Limit 0 offset`. The native side limit already allows a walls-measurable shift `n`, so the
relifted collar is consumed directly:

* `shiftChart_facts`: a relifted chart keeps conformality, its derivative logarithm (shifted by `−2πim`) and the
  lift identity;
* **`late_sideLimits_offExcShift`**: `late_sideLimits_offExc` with the collar in the chart
  `shiftChart baseChart m` (`SideC18.collarAtExcWithChart`); conclusion `SideTarget.Limit m offset`.

The active complement and the relative chart's inverse do not see the lift, so the measurability and boundary
inputs are the base chart's. Conditional helper with a distinct name; nothing here uses Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open Complex (I)
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm5

open Current Sec7 LocalSets WangWu WholeField Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt Sec7.Aux119Heights Sec7.PhaseSel

/-- **A relifted chart keeps the analytic chart facts**: conformality (which does not see the lift), the derivative
logarithm shifted by `−2πin`, and the lift identity for the shifted logarithm. -/
theorem shiftChart_facts {c : Chart} {ℓ : ℂ → ℂ} (n : ℤ)
    (h : c.IsConformal ∧ IsDerivLog c.1 ℓ c.dom ∧ ∀ z ∈ c.dom, c.2.2 z = (ℓ z).im) :
    (Sec7.PocketStopField.shiftChart c n).IsConformal ∧
      IsDerivLog (Sec7.PocketStopField.shiftChart c n).1 (fun z => ℓ z - n * (2 * π * I))
        (Sec7.PocketStopField.shiftChart c n).dom ∧
      ∀ z ∈ (Sec7.PocketStopField.shiftChart c n).dom,
        (Sec7.PocketStopField.shiftChart c n).2.2 z = (ℓ z - n * (2 * π * I)).im := by
  refine ⟨h.1, isDerivLog_sub_int h.2.1 n, fun z hz => ?_⟩
  show c.2.2 z - 2 * π * n = _
  rw [im_sub_int_mul, h.2.2 z hz]

/-- **`late_sideLimits_offExc` with the collar in R100's relifted current chart** (PROVE-T12-ASSEMBLE5). The collar is
asked in the chart `shiftChart baseChart m` for a walls-measurable integer `m` (`SideC18.collarAtExcWithChart`, the
form `SideC18.LateSideCollarExcShift` provides at every capacity); the conclusion is the native side limit with the
same shift `m` and the side data's offset. All other inputs are `late_sideLimits_offExc`'s. -/
theorem late_sideLimits_offExcShift {Ω : Type} [mΩ : MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (j : SideTest Ω) (e : Late.SideData Ω) (m : Ω → ℤ) (hm : Measurable[(j.target i d).walls] m)
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
    (hCollarExc : ∀ q : ℝ≥0, SideC18.collarAtExcWithChart j i d e
      (fun ω => Sec7.PocketStopField.shiftChart ((j.target i d).baseChart ω) (m ω)) X q)
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
      ∃ i, 0 < e.visit i ω ∧ (e.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ e.event i) :
    ∃ (n : Ω → ℤ) (a : ℝ), Measurable[(j.target i d).walls] n ∧
      ∀ q : ℝ≥0, (j.target i d).Limit n a q := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  have hκ : 4 < 16 / (16 / i.kappa) := by rw [hdual]; exact i.kappa_gt_four
  have hκ0 : 0 < 16 / (16 / i.kappa) := by linarith
  have hbase := fun ω (hω : ω ∈ (j.target i d).event) => SideTest.baseChart_aux29Facts (i := i) hj hω
  refine ⟨m, e.offset, hm, ?_⟩
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
        (fun ω => Sec7.PocketStopField.shiftChart (pChart event
          (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) chart ω) (m ω)) s)
      (c := fun ω => Sec7.PocketStopField.shiftChart (pChart event
        (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) chart ω) (m ω))
      (a := e.offset) (δ := e.phase)
      hκ hDriven (fun ω _ => by rfl) (fun ω _ => by rfl)
      (fun q => Aux29Cor.pocketStopPhaseSideLimit_of_collar_offExc hκ0 hZero hpre hOpen hFo
        hRawReference (hLattice q) hDriven
        (ℓ := fun ω z => pLog event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed))
          chart ω z - (m ω) * (2 * π * I))
        (fun ω hω => shiftChart_facts (m ω) (hbase ω hω).1)
        (fun ω hω => (hbase ω hω).2.1)
        (fun ω hω => (hbase ω hω).2.2) (hKm q) hu hub (hX q) (hCollarExc q))
      hProbes hJointGerms hVisits
    exact hs q
  · have hs := pocketStopSideLimit_of_phase_probes_joint_germs
      (P := d.measure) (ρL := wordL2 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight))
      (ρR := wordR2 (16 / i.kappa) (rs136Theta2 (16 / i.kappa) i.rightWeight))
      (xL := marksL2All d.rightWall chart)
      (xR := marksRAll (d.leftWall seed) (StripSys.rt seed) chart)
      (K := fun s => activeCompl event
        (if infinite then travAllInf d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart
          else travAll d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart)
        (fun ω => Sec7.PocketStopField.shiftChart (pChart event
          (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) chart ω) (m ω)) s)
      (c := fun ω => Sec7.PocketStopField.shiftChart (pChart event
        (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) chart ω) (m ω))
      (a := e.offset) (δ := e.phase)
      hκ hDriven (fun ω _ => by rfl) (fun ω _ => by rfl)
      (fun q => Aux29Cor.pocketStopPhaseSideLimit_of_collar_offExc hκ0 hZero hpre hOpen hFo
        hRawReference (hLattice q) hDriven
        (ℓ := fun ω z => pLog event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed))
          chart ω z - (m ω) * (2 * π * I))
        (fun ω hω => shiftChart_facts (m ω) (hbase ω hω).1)
        (fun ω hω => (hbase ω hω).2.1)
        (fun ω hω => (hbase ω hω).2.2) (hKm q) hu hub (hX q) (hCollarExc q))
      hProbes hJointGerms hVisits
    exact hs q

end InteractingSLE.Wire.T12Asm5
