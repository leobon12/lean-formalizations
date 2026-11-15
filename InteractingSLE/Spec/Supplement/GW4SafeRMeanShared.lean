/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRNextWire

/-!
# GW4: shared interface for component locality and its finite-word mean

PROVE-GW4-CLOC supplies `GW4ComponentLocalityStatement`; PROVE-GW4-SAFER
supplies `GW4ComponentMeanStatement`. Neither assertion is proved by defining
it. The assembler below combines their actual proofs into the unchanged
`GW4ComponentLinesStatement`. Locality witnesses are unrestricted: no clipped
set or particular harmonic-extension choice is imposed on the locality proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.RelSafe Supp8.Q3Stop Exist.StagedLaw Sec7.StripSysField GW4Rel GW4Traverse

/-- Exactly the locality and shape clauses of `HasComponentLines`, for the
witnesses chosen by the conditional component-locality argument. -/
def ComponentLineLocality {Ω : Type*} [mΩ : MeasurableSpace Ω] (c₀ : BoundaryWord)
    (F : Frame) (ν : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (hWm : ∀ r, Measurable (Wd r)) (u₀ : ℂ → ℝ)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ) : Prop :=
  IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀ ∧
  (∀ t, physFilt Frame.measurable_gw4Rec hWm ν t ≤ ℋ t) ∧
  (∀ t, ℋ t ≤ mΩ) ∧ (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧
  (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
  (∀ t, IsHistoryAvoidanceLocal (ℋ t) (B t) (centredField X u₀) ν) ∧
  ∀ t, ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
    H \ B t ω = H \ fwdHull (fun r : ℝ => R r.toNNReal ω)
      (lineClock F Wd GT V t ω).toNNReal

/-- Exactly the zero-phase finite-word mean clause of `HasComponentLines`.
The assertion concerns every version of the local-set mean of the same `B`. -/
def ComponentLineMean {Ω : Type*} [MeasurableSpace Ω] (k : ℝ) (c₀ : BoundaryWord)
    (F : Frame) (ν : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (u₀ : ℂ → ℝ) (B : ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ t (g : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (B t) (centredField X u₀) ν g →
    ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
        (lineClock F Wd GT V t ω).toNNReal) →
      (g ω + smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ z, couplingMean k (fun r : ℝ => R r.toNNReal ω)
          (lineClock F Wd GT V t ω).toNNReal
          (bheProc k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀)) R
            (componentVL k c₀ X R V) (componentVR k c₀ X R V) ω
            (lineClock F Wd GT V t ω).toNNReal) z * ψ z

/-- The two local interfaces assemble without changing any clause. -/
theorem hasComponentLines_of_locality_mean {Ω : Type*} [MeasurableSpace Ω]
    {k : ℝ} {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
    {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)} {u₀ : ℂ → ℝ}
    {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hl : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hm : ComponentLineMean k c₀ F ν X Wd GT R V u₀ B) :
    HasComponentLines k c₀ F ν X Wd GT R V hWm := by
  obtain ⟨hu₀, hphys, hℋ, hBm, hBc, hloc, hshape⟩ := hl
  exact ⟨u₀, ℋ, B, hu₀, hphys, hℋ, hBm, hBc, hloc, hshape, hm⟩

/-- The common original-GW4 quantifiers. A local predicate is evaluated in the
actual conditional component, frame and path-rule version. -/
def GW4ComponentProperty (Φ : ∀ {Ω : Type u} [MeasurableSpace Ω],
    (k : ℝ) → (c₀ : BoundaryWord) → (F : Frame) → (ν : Measure Ω) →
    (X : Ω → DistOn upperHalfPlaneOpens) → (Wd : ℝ≥0 → Ω → ℝ) → (GT : Set Ω) →
    (R : ℝ≥0 → Ω → ℝ) → (V : Ω → ℝ≥0∞) → (∀ r, Measurable (Wd r)) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔
            pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L,
        ∀ (c : Chart) (hC : Ω → DistOn upperHalfPlaneOpens)
          (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b
            (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
        ∀ c₀ : BoundaryWord, c₀.IsSorted → c₀.jumps = counterflowJumps jumpsC →
          (∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) →
        ∀ (F : Frame) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω),
          F.IsOk → F.C = C → F.c = c →
          (∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) →
        ∀ hWm : ∀ r, Measurable (Wd r), MeasurableSet GT → (∀ᵐ ω ∂ν, ω ∈ GT) →
          (∀ᵐ ω ∂ν, ∀ t, Wd t ω = W' t ω) →
        ∀ (Rv : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞),
          IsGW4RelVersionR ν Wd F.c F.C Rv V →
          Φ (16 / κ) c₀ F ν (fun ω => invField κ (hC ω)) Wd GT Rv V hWm

/-- CLOC's global target: the component line witnesses, without the mean clause. -/
def GW4ComponentLocalityStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ _ c₀ F ν X Wd GT R V hWm =>
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B

/-- SAFER's global target: the actual finite-word mean with zero phase, for
any witnesses satisfying the component-locality half. -/
def GW4ComponentMeanStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ k c₀ F ν X Wd GT R V hWm =>
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B →
      ComponentLineMean k c₀ F ν X Wd GT R V u₀ B

/-- The separate locality and mean proofs plug into the existing GW4 consumer. -/
theorem gw4ComponentLinesStatement_of_locality_mean
    (hL : GW4ComponentLocalityStatement.{u}) (hM : GW4ComponentMeanStatement.{u}) :
    GW4ComponentLinesStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hM κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hl hm
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver
  obtain ⟨u₀, ℋ, B, hloc⟩ := hl C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver
  exact hasComponentLines_of_locality_mean hloc
    (hm C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
      F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver u₀ ℋ B hloc)

end InteractingSLE.Theorem14.GW4Fix
