/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2DynR1

/-!
# Remaining boundary dynamics for first-contact K2

The exposed-side seed and interior pre-lifetime collision checks are proved.
The residual below explicitly retains capacity safe laws, collapsed-side seed
bounds and boundary collision checks. It is not asserted true here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open RetAux79 DomainMarkov.K2 Sec7.PocketTraversal
universe u
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Exact residual at one canonical chart path. `collapsed_seed` is needed
only when an exposed interval collapses. `boundary` is needed only at positive
noninterior tips. The retained-chart member identities proved in `FCK2DynR1`
have not been transferred to these capacity windows. -/
structure FCK2DynBoundaryInputs (P : Measure Ω) (κ θ : ℝ) (d : PairData Ω)
    (β : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (U : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) (W : ℝ≥0 → Ω → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  collapsed_seed : ∀ᵐ ω ∂P, ω ∈ meetSet d → d.wordL ω = 0 ∨ d.wordR ω = 0 →
    ExplState.IsAdmissibleSeed κ
      (PiecewiseConstantBoundaryData.leftLim (β ω).fn 0)
      (PiecewiseConstantBoundaryData.rightLim (β ω).fn 0) θ
  safe_law : ∀ a : ForceWordType,
    HasSafeLaw κ a.rhoL a.rhoR P 𝓕 (fcTypeBranch κ θ (meetSet d) β a) U W
      (geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
      (geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
      (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  safe_members : HasSafeMembers P 𝓕 (meetSet d) U W
    (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  boundary : ∀ a : ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ (meetSet d) β a →
    ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < U ω → γ ω t ∉ QuantumZipper.H →
      ¬ ForceWord.ThresholdCondition a.rhoL a.rhoR (W t ω)
        (fun i => geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) i t ω)
        (fun j => geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) j t ω)
  terminal : ∀ a : ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ (meetSet d) β a →
    ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω → ForceWord.ThresholdCondition a.rhoL a.rhoR (W T ω)
      (fun i => geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) i T ω)
      (fun j => geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) j T ω)

/-- Assemble the original dynamics without an interior collision premise or
an exposed-side seed premise in the residual record. -/
theorem fck2SourceDynamics_of_boundaryInputs {P : Measure Ω} {κ θ : ℝ} (hκ : 0 < κ)
    {d : PairData Ω} (hd : d.IsMeasGood) {β : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {U : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    {W : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    (hc : ∀ ω, Continuous (W · ω)) (h0 : ∀ ω, W 0 ω = 0)
    (hg : ∀ᵐ ω ∂P, ω ∈ meetSet d → IsGeneratingTrace (W · ω) (U ω) (γ ω))
    (hexposed : ∀ᵐ ω ∂P, ω ∈ meetSet d → d.wordL ω < 0 → 0 < d.wordR ω →
      ExplState.IsAdmissibleSeed κ
        (PiecewiseConstantBoundaryData.leftLim (β ω).fn 0)
        (PiecewiseConstantBoundaryData.rightLim (β ω).fn 0) θ)
    (hb : FCK2DynBoundaryInputs P κ θ d β Hc U γ W 𝓕) :
    FCK2SourceDynamics P κ θ (meetSet d) β Hc U W 𝓕 := by
  have ha : ∀ᵐ ω ∂P, ω ∈ meetSet d → ExplState.IsAdmissibleSeed κ
      (PiecewiseConstantBoundaryData.leftLim (β ω).fn 0)
      (PiecewiseConstantBoundaryData.rightLim (β ω).fn 0) θ := by
    filter_upwards [hexposed, hb.collapsed_seed] with ω he hbω hω
    have hE := (mem_meetSet_iff.1 hω).1
    by_cases hL : d.wordL ω < 0
    · by_cases hR : 0 < d.wordR ω
      · exact he hω hL hR
      · exact hbω hω (Or.inr (le_antisymm (not_lt.1 hR) (hd.wordR_nonneg hE)))
    · exact hbω hω (Or.inl (le_antisymm (hd.wordL_nonpos hE) (not_lt.1 hL)))
  refine ⟨ha, hb.safe_law, hb.safe_members, ?_, hb.terminal⟩
  intro a
  apply prelifeNonThreshold_of_boundary_checks hc h0
    (fun ω => (FCDet.isOrderedForceWord_typeXL (β ω)).2.1)
    (fun ω => (FCDet.isOrderedForceWord_typeXL (β ω)).2.2.2)
    (hg.mono fun _ hω hB => hω hB.1) ?_ (hb.boundary a)
  filter_upwards [ha] with ω haω hB
  exact not_threshold_type_of_admissible hκ hB.2 (haω hB.1)

/-- Exact universal residual in the unchanged source context. This definition
is a named hypothesis, not a proof of the source capacity and boundary facts. -/
def FirstContactK2BoundaryInputsStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
      (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∀ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      ∀ (hm₁ : ∀ t, Measurable (W₁ t)) (hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      (FCK2DynBoundaryInputs P κ θ₁ d β (hd.chartField κ h) U₁ γ₁ W₁
        (fcRetainedDriverFiltration P hd W₁ hm₁)) ∧
        (FCK2DynBoundaryInputs P κ θ₂ d β (hd.chartField κ h) U₂ γ₂ W₂
          (fcRetainedDriverFiltration P hd W₂ hm₂))

/-- The original dynamics statement from the precise boundary residual.
Both exposed-side seed conclusions come from the source box mean theorem. -/
theorem firstContactK2DynamicsStatement_of_boundaryInputs
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) (hbnd : FirstContactK2BoundaryInputsStatement.{u}) :
    FirstContactK2DynamicsStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨B₁, B₂⟩ := hbnd κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  have hs := ae_admissible_of_boxMean_exposed h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hsort hmean
  exact ⟨fck2SourceDynamics_of_boundaryInputs hκ hd hc₁ hz₁
      (hg.mono fun _ hω hM => (hω hM).1)
      (hs.mono fun _ hω hM hL hR => (hω hM hL hR).1) B₁,
    fck2SourceDynamics_of_boundaryInputs hκ hd hc₂ hz₂
      (hg.mono fun _ hω hM => (hω hM).2)
      (hs.mono fun _ hω hM hL hR => (hω hM hL hR).2) B₂⟩

/-- Determination from Theorems 1.2–1.3, Lemma 7.6 and the still unproved
boundary/capacity residual. No unconditional determination is claimed. -/
theorem firstContactCanonCondDetStatement_of_boundaryInputs_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u}) (hbnd : FirstContactK2BoundaryInputsStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_dynamics_thm12_thm13_lemma76 h12 h13 h12₀ h13₀ h76
    (firstContactK2DynamicsStatement_of_boundaryInputs (lemma75Statement_of_thm12_thm13 h12 h13)
      (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76)
      firstContact_retainedRangeEntranceStatement hbnd)

end InteractingSLE.Restart.FCPlumb
