/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineIfaceR
import InteractingSLE.Spec.Supplement.SB2VdDrvAe
import InteractingSLE.Spec.Supplement.SB2VhLife
import InteractingSLE.Spec.Supplement.SB2VePhys
import InteractingSLE.Spec.Supplement.SB2TcFilt

/-!
# SB2(1)'s version half: the measurable version (named input)

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The assembly of
`Lv.SB2LineVersionRStatement` (`SB2VeAsm`) uses the landed per-sample results (the chain record `Vc.ae_lineGeom_liftOf`,
the clock `Vc.clockOf`, the physical driver `Ve.exists_physDriver`, E7 `Vh.SB2RemainderLifeStatement`, `reg`). The one
step not yet carried out is the **measurable construction** of the relative driver, trace and clock for the completed
line filtration, i.e. making the per-sample objects measurable: `Vd.ae_isDrivenCurve_lift` +
`Lk.exists_measurable_driver_of_drivenCurves`, the readings `Vh.relRead` + `Vc.measurable_of_dense_good_at`, the
capacity readings `measurable_hcapHit_range`, the forward clock `Lv.isRemainderLink_of_forwardClock`. It is stated here
as the named input **`SB2MeasVersionStatement`** with its exact type:

a driver `W` (continuous, from `0`, adapted to the time change `Tc.tcFilt` of the completed line filtration along a
clock `a`), a trace `Γ`, a lifetime `Vg`, a global Loewner trace `ηr` of `W`, a clock `a` (continuous, monotone, from
`0`, adapted to `D.lineFiltC`) with measurable safe events, such that almost surely at a launch on the entrance event:
`W` generates `Γ` up to `Vg` and `Γ + m` is linked to the flow; the clock is `Vc.clockOf` of the flow's lift `flowLift`;
`Vg` is the lift's relative lifetime; and `ηr` reads the lift in its capacity clock.

* `entT`, `flowLift`: the entrance time and the flow's lift `Vc.liftOf …` at a sample (abbreviations).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ve

open Lv Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal

/-- The entrance time `T_L` at a sample. -/
def entT {Ω : Type*} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (u : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))

/-- The flow's lift at a sample: `Vc.liftOf` in the shifted launch chart, from the entrance, off the shifted
retained prefix. -/
def flowLift {Ω : Type*} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (k : ℕ) (u : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℂ :=
  Vc.liftOf (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)) (η ω) u
    (entT κ b jumps E k u η ζ ω).toNNReal ((fun z => z - (u : ℂ)) '' lowerPrefix κ b jumps E (k + 1) u ω)

/-- **Named input: the measurable version** (the measurable construction of SB2(1)'s relative driver, trace and clock
for the completed line filtration; see the module docstring). -/
def SB2MeasVersionStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀),
    ∃ (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ) (Vg : Ω → ℝ≥0∞) (ηr : Ω → ℝ → ℂ) (a : ℝ≥0 → Ω → ℝ≥0∞)
      (ha : ∀ t, Measurable[D.lineFiltC HP t] (a t)),
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧
      (∀ ω, Continuous fun t => a t ω) ∧ (∀ ω, Monotone fun t => a t ω) ∧ (∀ ω, a 0 ω = 0) ∧
      StronglyAdapted (Tc.tcFilt (D.lineFiltC HP) a ha) W ∧
      (∀ w ∈ I.types, ∀ (φ : TestOn upperHalfPlaneOpens) t, MeasurableSet[D.lineFiltC HP t]
        {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
          Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) ∧
      (∀ w ∈ I.types, ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[D.lineFiltC HP t]
        {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
          Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → entT κ b jumps E k u η ζ ω < ζ ω →
        IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
        IsRemainderLink (Lv.launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω) ∧
        (∀ t, a t ω = Vc.clockOf (flowLift κ b jumps E k u η ζ ω) (entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t) ∧
        Vg ω = ⨆ (s : ℝ≥0) (_ : (((entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω),
          ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR (flowLift κ b jumps E k u η ζ ω)) s) ∧
        IsLoewnerTrace (fun r : ℝ => W r.toNNReal ω) (ηr ω) ∧
        ∀ s : ℝ≥0, (((entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
          ηr ω (Sec7.Lemma71C.capClock (Vd.liftR (flowLift κ b jumps E k u η ζ ω)) s) =
            flowLift κ b jumps E k u η ζ ω s

end InteractingSLE.Theorem14.SB.Ve
