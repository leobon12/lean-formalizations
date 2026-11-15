/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkAsm
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DwVkLink
import InteractingSLE.Spec.Supplement.SB2VkLink
import InteractingSLE.Spec.Supplement.SBS3DwViRed
import InteractingSLE.Spec.Supplement.SB2ViRed
import InteractingSLE.Spec.Supplement.SBS3DwDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DwTcRec
import InteractingSLE.Spec.Supplement.SBS3DwVcAe
import InteractingSLE.Spec.Supplement.SBS3DwVdAe
import InteractingSLE.Spec.Supplement.SBS3DwVdDrvAe
import InteractingSLE.Spec.Supplement.SBS3DwVeAsm
import InteractingSLE.Spec.Supplement.SBS3DwVeIn
import InteractingSLE.Spec.Supplement.SBS3DwVfReadAe
import InteractingSLE.Spec.Supplement.SBS3DwVgBad
import InteractingSLE.Spec.Supplement.SBS3DwVgCap
import InteractingSLE.Spec.Supplement.SBS3DwVgClock
import InteractingSLE.Spec.Supplement.SBS3DwVgDense
import InteractingSLE.Spec.Supplement.SBS3DwVhLife
import InteractingSLE.Spec.Supplement.SBS3DwViAbs
import InteractingSLE.Spec.Supplement.SBS3DwVjEnt
import InteractingSLE.Spec.Supplement.SBS3DwVjJoint
import InteractingSLE.Spec.Supplement.SBS3DwVjRel
import InteractingSLE.Spec.Supplement.SBS3DwVkEnd
import InteractingSLE.Spec.Supplement.SBS3DwVkFam
import InteractingSLE.Spec.Supplement.SBS3DwVkFrz
import InteractingSLE.Spec.Supplement.SBS3DwVkLife

/-!
# Successor of `SB2VkAsm` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). The declarations of `SB2VkAsm` that use Lemma S3 in SB2(1)'s form,
restated so that Lemma S3 enters as `Tc.SB2EntranceNoCommonArcLeStatement` (upper angle `ψ ≤ π/2`, PROVED
from Theorems 1.2–1.3 as `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). Every launch problem carries the bound
as an instance argument `[Fact (ψ ≤ Real.pi / 2)]`; the proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `exists_driverDataLe`;
* `SB2DriverAdaptLeStatement`;
* `sb2DriverVersionStatement_of_adaptLe`;
* `sb2LineVersionRStatement_of_adaptLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop
  Sec7.PocketTraversal Sec7.Lemma71C

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The driver data** for a measurable clock that is almost surely the lift's clock. -/
theorem exists_driverDataLe (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u})
    (hEnd : SB2RelEndpointLeStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) [Fact (ψ ≤ Real.pi / 2)]
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    {a : ℝ≥0 → Ω → ℝ≥0∞} (ha : ∀ t, Measurable (a t))
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
        (ζ ω) t) :
    ∃ (ρ : Ω → ℝ → ℂ) (W : ℝ≥0 → Ω → ℝ) (G : Set Ω) (Γ : Ω → ℝ≥0 → ℂ) (Vg : Ω → ℝ≥0∞) (ηr : Ω → ℝ → ℂ),
      (∀ r, 0 ≤ r → Measurable fun ω => ρ ω r) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) ∧
      MeasurableSet G ∧ P Gᶜ = 0 ∧
      (∀ q, Measurable (W q)) ∧ (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun q => W q ω) ∧
      (∀ q ω, ω ∉ G ∩ D.event → W q ω = 0) ∧
      (∀ ω ∈ G ∩ D.event, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω ∧
        IsDrivenCurve (ρ ω) ∧ Sec7.Lemma71C.capLife (ρ ω) = relLife κ b jumps E k u η ζ ω ∧
        ∀ q : ℝ≥0, (q : ℝ≥0∞) < relLife κ b jumps E k u η ζ ω → W q ω = segDriver (ρ ω) q) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
        IsRemainderLink (Lv.launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω) ∧
        Vg ω = ⨆ (s : ℝ≥0) (_ : (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω),
          ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s) ∧
        IsLoewnerTrace (fun r : ℝ => W r.toNNReal ω) (ηr ω) ∧
        ∀ s : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
          ηr ω (Sec7.Lemma71C.capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s) =
            Ve.flowLift κ b jumps E k u η ζ ω s := by
  classical
  obtain ⟨ρ, hρm, hρ⟩ := exists_drivenFamilyLe h13 hS3 HP I D ha hae
  obtain ⟨W, G, hGm, hGnull, hWm, hW0, hWc, hWoff, hWon⟩ := exists_frozenDriverLe h13 hS3 hEnd HP D hρm hρ
  have hηex : ∀ ω, ∃ ηr : ℝ → ℂ, ω ∈ G ∩ D.event → IsLoewnerTrace (fun r : ℝ => W r.toNNReal ω) ηr ∧
      ∀ s : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
        ηr (Sec7.Lemma71C.capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s) =
          Ve.flowLift κ b jumps E k u η ζ ω s := fun ω => by
    by_cases hω : ω ∈ G ∩ D.event
    · obtain ⟨ηr, h1, h2⟩ := (hWon ω hω).2.2.2.2.2.2.2
      exact ⟨ηr, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' hω⟩
  choose ηr hηr using hηex
  refine ⟨ρ, W, G, fun ω => frz (capTrace (ρ ω)) (relLife κ b jumps E k u η ζ ω),
    relLife κ b jumps E k u η ζ, ηr, hρm, hρ, hGm, hGnull, hWm, hW0, hWc, hWoff, fun ω hω => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, -⟩ := hWon ω hω
    exact ⟨h1, h2, h3, h4, h5⟩
  · have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGnull
    filter_upwards [hGae, D.ae_mem_event_iff, hρ, ae_lift_chartLe h13 hS3 HP] with ω hωG hev hρω hch hl hT
    have hω : ω ∈ G ∩ D.event := ⟨hωG, (hev hl).2 hT⟩
    obtain ⟨-, -, hd, hcl, -, hfin, hgen, -⟩ := hWon ω hω
    obtain ⟨hη1, hη2⟩ := hηr ω hω
    obtain ⟨h1, h2⟩ := hρω hl hT
    have hlink := isRemainderLink_frz (c := Lv.launchChart κ b jumps E (k + 1) ω) (η := η ω) (Z := ζ ω)
      (L := realMin (lowerPrefix κ b jumps E (k + 1) u ω)) (m := launchEntry κ b jumps E (k + 1) u ω)
      (γ := Ve.flowLift κ b jumps E k u η ζ ω) hd h1 h2 (fun h' => hfin (hcl ▸ h')) (hch hl hT)
    rw [hcl] at hlink
    exact ⟨hgen, hlink, rfl, hη1, hη2⟩

end

/-- **The remaining clauses of the driver statement**: for a clock as in `Vi.SB2DriverVersionLeStatement` and every
driver with the structural properties of `exists_driverDataLe` (measurable, from `0`, continuous, `0` off a measurable
conull `G` intersected with the entrance event, the canonical driver of a measurable driven family that reads the lift
before the relative lifetime), the driver is adapted to the time-changed completed line filtration and the two safe
events are measurable for the completed line filtration. -/
def SB2DriverAdaptLeStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    [Fact (ψ ≤ Real.pi / 2)] (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (a : ℝ≥0 → Ω → ℝ≥0∞)
    (ha : ∀ t, Measurable[D.lineFiltC HP t] (a t)),
    (∀ ω, Continuous fun t => a t ω) → (∀ ω, Monotone fun t => a t ω) → (∀ ω, a 0 ω = 0) →
    (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
        (ζ ω) t) →
    ∀ (ρ : Ω → ℝ → ℂ) (W : ℝ≥0 → Ω → ℝ) (G : Set Ω), (∀ r, 0 ≤ r → Measurable fun ω => ρ ω r) →
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) →
      MeasurableSet G → P Gᶜ = 0 →
      (∀ q, Measurable (W q)) → (∀ ω, W 0 ω = 0) → (∀ ω, Continuous fun q => W q ω) →
      (∀ q ω, ω ∉ G ∩ D.event → W q ω = 0) →
      (∀ ω ∈ G ∩ D.event, ω ∈ launchSet κ b jumps E (k + 1) ∧ Ve.entT κ b jumps E k u η ζ ω < ζ ω ∧
        IsDrivenCurve (ρ ω) ∧ Sec7.Lemma71C.capLife (ρ ω) = relLife κ b jumps E k u η ζ ω ∧
        ∀ q : ℝ≥0, (q : ℝ≥0∞) < relLife κ b jumps E k u η ζ ω → W q ω = segDriver (ρ ω) q) →
      StronglyAdapted (Tc.tcFilt (D.lineFiltC HP) a ha) W ∧
      (∀ w ∈ I.types, ∀ (φ : TestOn upperHalfPlaneOpens) t, MeasurableSet[D.lineFiltC HP t]
        {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
          Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) ∧
      (∀ w ∈ I.types, ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[D.lineFiltC HP t]
        {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
          Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})

/-- **The driver statement from Theorem 1.3, S3, the relative endpoint and the remaining clauses.** -/
theorem sb2DriverVersionStatement_of_adaptLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (hEnd : SB2RelEndpointLeStatement.{u})
    (hAd : SB2DriverAdaptLeStatement.{u}) : Vi.SB2DriverVersionLeStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP _ I u₀ D a ha hac ham ha0 hae
  have ha' : ∀ t, Measurable (a t) := fun t => (ha t).mono ((D.lineFiltC HP).le t) le_rfl
  obtain ⟨ρ, W, G, Γ, Vg, ηr, hρm, hρ, hGm, hGnull, hWm, hW0, hWc, hWoff, hWon, hdr⟩ :=
    exists_driverDataLe h13 hS3 hEnd HP I D ha' hae
  obtain ⟨hWad, hsS, hsL⟩ := hAd κ b jumps P h E k u ψ η ζ HP I u₀ D a ha hac ham ha0 hae ρ W G hρm hρ hGm
    hGnull hWm hW0 hWc hWoff hWon
  exact ⟨W, Γ, Vg, ηr, hW0, hWc, hWad, hsS, hsL, hdr⟩

/-- **SB2(1)'s line version** (`Lv.SB2LineVersionRLeStatement`) from Theorem 1.3, S3, E7, the relative endpoint and
the remaining clauses. -/
theorem sb2LineVersionRStatement_of_adaptLe (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) (hE7 : Vh.SB2RemainderLifeLeStatement.{u})
    (hEnd : SB2RelEndpointLeStatement.{u}) (hAd : SB2DriverAdaptLeStatement.{u}) :
    Lv.SB2LineVersionRLeStatement.{u} :=
  Vi.sb2LineVersionRStatement_of_driverLe h13 hS3 hE7 (sb2DriverVersionStatement_of_adaptLe h13 hS3 hEnd hAd)

end InteractingSLE.Theorem14.SB.Vk
