/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VgClock
import InteractingSLE.Spec.Supplement.SB2VeAsm

/-!
# SB2(1)'s version half: the measurable version reduced to its driver part

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). Round 9 built the version's clock
(`Vg.exists_versionClock`). The remaining content of `Ve.SB2MeasVersionStatement` is the **driver part**, named here
with its exact type, **`SB2DriverVersionStatement`**: for every clock `a` with the properties of
`exists_versionClock` (measurable for `D.lineFiltC`, continuous, monotone, `0` at `0`, a.s. the relative clock of the
flow's lift), there are a driver `W` (continuous, from `0`, adapted to `Tc.tcFilt (D.lineFiltC) a`), a trace `Γ`, a
lifetime `Vg` and a global Loewner trace `ηr`, with the safe events measurable, and almost surely at a launch on the
entrance event: `W` generates `Γ` up to `Vg`, `Γ + m` is linked to the flow, `Vg` is the lift's relative lifetime,
and `ηr` reads the lift in its capacity clock.

* **`sb2MeasVersionStatement_of_driver`**: `Ve.SB2MeasVersionStatement` from Theorem 1.3, Lemma S3 (SB2(1)'s form) and
  `SB2DriverVersionStatement`.

So `Lv.SB2LineVersionRStatement` follows from Theorem 1.3, S3, E7 and `SB2DriverVersionStatement`
(`sb2LineVersionRStatement_of_driver`). R48: Theorem 1.3 as a hypothesis; serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vi

open Lv Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal Ve

/-- **Named input: the driver part of the measurable version** (see the module docstring). -/
def SB2DriverVersionStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (a : ℝ≥0 → Ω → ℝ≥0∞)
    (ha : ∀ t, Measurable[D.lineFiltC HP t] (a t)),
    (∀ ω, Continuous fun t => a t ω) → (∀ ω, Monotone fun t => a t ω) → (∀ ω, a 0 ω = 0) →
    (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (flowLift κ b jumps E k u η ζ ω) (entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t) →
    ∃ (W : ℝ≥0 → Ω → ℝ) (Γ : Ω → ℝ≥0 → ℂ) (Vg : Ω → ℝ≥0∞) (ηr : Ω → ℝ → ℂ),
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧
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
        Vg ω = ⨆ (s : ℝ≥0) (_ : (((entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω),
          ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR (flowLift κ b jumps E k u η ζ ω)) s) ∧
        IsLoewnerTrace (fun r : ℝ => W r.toNNReal ω) (ηr ω) ∧
        ∀ s : ℝ≥0, (((entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
          ηr ω (Sec7.Lemma71C.capClock (Vd.liftR (flowLift κ b jumps E k u η ζ ω)) s) =
            flowLift κ b jumps E k u η ζ ω s

/-- **The measurable version from its driver part** (the clock is `Vg.exists_versionClock`). -/
theorem sb2MeasVersionStatement_of_driver (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (hDV : SB2DriverVersionStatement.{u}) :
    SB2MeasVersionStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ D
  obtain ⟨a, ha, hac, ham, ha0, hae⟩ := Vg.exists_versionClock h13 hS3 HP I D
  obtain ⟨W, Γ, Vg, ηr, hW0, hWc, hWad, hsS, hsL, hdr⟩ :=
    hDV κ b jumps P h E k u ψ η ζ HP I u₀ D a ha hac ham ha0 hae
  refine ⟨W, Γ, Vg, ηr, a, ha, hW0, hWc, hac, ham, ha0, hWad, hsS, hsL, ?_⟩
  filter_upwards [hdr, hae] with ω hd hc hF hT
  obtain ⟨h1, h2, h3, h4, h5⟩ := hd hF hT
  exact ⟨h1, h2, hc hF hT, h3, h4, h5⟩

/-- **`SB2LineVersionRStatement` from Theorem 1.3, S3, E7 and the driver part.** -/
theorem sb2LineVersionRStatement_of_driver (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (hE7 : Vh.SB2RemainderLifeStatement.{u})
    (hDV : SB2DriverVersionStatement.{u}) : SB2LineVersionRStatement.{u} :=
  sb2LineVersionRStatement_of_inputs h13 hS3 hE7 (sb2MeasVersionStatement_of_driver h13 hS3 hDV)

end InteractingSLE.Theorem14.SB.Vi
