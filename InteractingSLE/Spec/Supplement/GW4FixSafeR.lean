/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixPhysCoord

/-!
# GW4's relative safe law for path-rule versions

Packet PROVE-T14-GW4FIX (continuation). As for GB6 (`Q3Stop.GB6RelSafeRStatement`, PROVE-GB6-RELSAFE), the relative
safe law is needed only for versions whose stop is a measurable path rule of the relative path: an arbitrary
version's stop is only almost surely a stopping time of the completed relative path, and its physical readability
would need the predictability argument PROVE-Q3-REL4 found unavailable. Every version used downstream (the announced
coordinate versions, `gw4RelVersionAStatement_of_coord`) is of this form.

* `IsGW4RelVersionR`: a version through a stopping time whose stop is almost surely a measurable path rule;
* **`GW4RelSafeRStatement`** (named input): `GW4RelSafeStatement` restricted to these versions (implied by it,
  `gw4RelSafeRStatement_of_relSafe`);
* **`gw4RelativeLawRegStatement_of_relSafeR`**: Theorem GW4's component (Det) from `GW4RelSafeRStatement` alone (with
  the walks' barrier and pocket shape, GW3's word bounds and Theorems 1.2–1.3; the measurable coordinates are proved,
  `gw4RelCoordStatement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Rel Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId Supp8.Q3Stop Restart
  Sec7.StripSysField

/-- **A path-rule version of GW4's relative traversal**: a version through a stopping time whose stop is almost
surely a measurable path rule of the relative path. -/
def IsGW4RelVersionR {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (c : Chart) (C : Set ℂ)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  IsGW4RelStopVersion ν W' c C R V ∧
    ∃ ρ : (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable ρ ∧ IsPathRule₀ ρ ∧ ∀ᵐ ω ∂ν, V ω = ρ fun u => R u ω

theorem IsGW4RelVersionA.isGW4RelVersionR {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {W' : ℝ≥0 → Ω → ℝ}
    {c : Chart} {C : Set ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (h : IsGW4RelVersionA ν W' c C R V) :
    IsGW4RelVersionR ν W' c C R V :=
  ⟨h.1, h.2.2.1⟩

/-- **Named input: GW4's relative safe law for path-rule versions** (`GW4RelSafeStatement` with
`IsGW4RelVersionR` in place of `IsGW4RelStopVersion`; source as there). -/
def GW4RelSafeRStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ c₀ : BoundaryWord, c₀.IsSorted → c₀.jumps = counterflowJumps jumpsC →
            (∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) →
          ∀ (Rv : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), IsGW4RelVersionR ν W' c C Rv V →
            HasRelSafe (16 / κ) (wordType (16 / κ) c₀) (fun _ => c₀) univ
              (ν.map fun ω => (gw4Rec, relVar (fun ω => invField κ (hC ω)) Rv V ω))

/-- The general safe law implies the path-rule form. -/
theorem gw4RelSafeRStatement_of_relSafe (hS : GW4RelSafeStatement.{u}) : GW4RelSafeRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hSω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ Rv V hver
  exact hSω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ Rv V hver.1

/-- **The relative stopped match from announced versions and the path-rule safe law.** -/
theorem gw4RelStopMatchStatement_of_relSafeR (hV : GW4RelVersionAStatement.{u}) (hS : GW4RelSafeRStatement.{u}) :
    GW4RelStopMatchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hV κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hVω hSω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ F hF
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨Rv, V, hver, hexh⟩ := hVω C hCm c hch
  refine ⟨Rv, V, fun m => (hver m).1.1, hexh, fun m => ?_⟩
  have hR := (hver m).isGW4RelVersionR
  obtain ⟨hsv, hV0, ⟨ρ, hρm, hρ, hVρ⟩, ρs, hρsm, hρs, hρsfin, hρsmono, hann⟩ := hver m
  have hk : 0 < 16 / κ := sixteen_div_pos hκ
  have hm := ae_isStopDrvMatch_of_hasRelSafe (P := ν) hk hF (β := fun _ => c₀) measurable_const
    MeasurableSet.univ (wordType (16 / κ) c₀) (rec := fun _ => gw4Rec) measurable_const
    ((measurable_invField κ).comp hgff.1) hsv.1.1 hsv.1.2.1 hsv.1.2.2.1 hsv.1.2.2.2.1
    (hSω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ (Rv m) (V m) hR)
    (hV0.mono fun ω h _ => h) (ρ := fun x => ρ x.2) (hρm.comp measurable_snd) (isPathRule_comp_snd hρ) hVρ
    (ρs := fun n x => ρs n x.2) (fun n => (hρsm n).comp measurable_snd) (fun n => isPathRule_comp_snd (hρs n))
    (fun n x => hρsfin n x.2) (fun x => hρsmono x.2) (hann.mono fun ω h _ => h.1) (hann.mono fun ω h _ => h.2)
  filter_upwards [hm] with ω hω using hω (mem_univ _) rfl

/-- **Theorem GW4's component (Det) from the path-rule safe law alone** (conditional helper with a distinct name):
`GW4Reg.GW4RelativeLawRegStatement` from the walks' barrier with its pocket shape, GW3's word bounds, Theorems 1.2–1.3
and `GW4RelSafeRStatement`; the measurable relative coordinates are proved (`gw4RelCoordStatement`). -/
theorem gw4RelativeLawRegStatement_of_relSafeR (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hS : GW4RelSafeRStatement.{u}) :
    GW4Reg.GW4RelativeLawRegStatement.{u} :=
  gw4RelativeLawRegStatement_of_stopMatch h12 h13 h12₀ h13₀ hB hWB
    (gw4RelStopMatchStatement_of_relSafeR (gw4RelVersionAStatement_of_coord h13 hB (gw4RelCoordStatement h13 hB)) hS)

end InteractingSLE.Theorem14.GW4Fix
