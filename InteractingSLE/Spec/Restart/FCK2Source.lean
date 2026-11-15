/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2SourceCollision

/-!
# Source K2 data: proved initial fields and remaining dynamics

The force-type bounds and initial Gaussian laws are proved from the full source
context and box mean identification. The residual below retains only the
incident-height, safe-law and collision-geometry assertions. It is explicitly
a named hypothesis, not a theorem asserting those source assertions.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb
open RetAux79 DomainMarkov.K2 LocalSets Sec7.PocketTraversal
universe u
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Exact remaining source assertions. Finite force types and initial pairing
Gaussian laws are absent because they are proved in the preceding modules.
The collision fields describe states before and at death, rather than assuming
the desired equality of lifetime and first threshold. -/
structure FCK2SourceDynamics (P : Measure Ω) (κ θ : ℝ) (M : Set Ω)
    (β : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (U : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  admissible : ∀ᵐ ω ∂P, ω ∈ M → ExplState.IsAdmissibleSeed κ
    (PiecewiseConstantBoundaryData.leftLim (β ω).fn 0)
    (PiecewiseConstantBoundaryData.rightLim (β ω).fn 0) θ
  safe_law : ∀ a : ForceWordType,
    HasSafeLaw κ a.rhoL a.rhoR P 𝓕 (fcTypeBranch κ θ M β a) U W
      (geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
      (geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
      (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  safe_members : HasSafeMembers P 𝓕 M U W (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  prelife : ∀ a : ForceWordType, RetPrelifeNonThreshold (P := P) a.rhoL a.rhoR W
    (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω))
    (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) U (fcTypeBranch κ θ M β a)
  terminal : ∀ a : ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ M β a →
    ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω → ForceWord.ThresholdCondition a.rhoL a.rhoR (W T ω)
      (fun i => geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) i T ω)
      (fun j => geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) j T ω)

/-- Construct the full source record. The finite palette and initial Gaussian
pairing laws here are consequences of the box mean hypothesis, not hypotheses
of this theorem. The remaining dynamics have their separate exact type above. -/
theorem fck2SourceData_of_boxMean_and_dynamics
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma d P] β)
    (hs : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hm : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    (W : ℝ≥0 → Ω → ℝ) (hW : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (W · ω)) (h0 : ∀ ω, W 0 ω = 0) {θ : ℝ} {U : Ω → ℝ≥0∞}
    (hdyn : FCK2SourceDynamics P κ θ (meetSet d) β (hd.chartField κ h) U W
      (fcRetainedDriverFiltration P hd W hW)) :
    Nonempty (FCK2SourceData P κ θ (meetSet d) β (hd.chartField κ h) U W
      (fcRetainedDriverFiltration P hd W hW)) := by
  obtain ⟨N, heights, hbound⟩ := exists_ae_boundedForceTypes_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh
    hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hs hm
  exact ⟨{
    max_marks := N
    weights := flowWeightPalette κ θ heights
    bounded_types := hbound.mono fun _ hb hω => hb hω θ
    initial_gaussian := initialPairingGaussian_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂
      hd hζ₁ hζ₂ hae hu₀ hβ hs hm W hW h0 θ
    admissible := hdyn.admissible
    safe_law := hdyn.safe_law
    safe_members := hdyn.safe_members
    collision_lifetime := fun a => ae_life_eq_thr_of_preterminal hc (hdyn.prelife a) (hdyn.terminal a) }⟩


/-- The universal residual has the full original source context. Its two
conclusions retain only the exact dynamics fields above. This definition is
not a proof of their existence from that context. -/
def FirstContactK2DynamicsStatement : Prop :=
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
      (FCK2SourceDynamics P κ θ₁ (meetSet d) β (hd.chartField κ h) U₁ W₁
        (fcRetainedDriverFiltration P hd W₁ hm₁)) ∧
        (FCK2SourceDynamics P κ θ₂ (meetSet d) β (hd.chartField κ h) U₂ W₂
          (fcRetainedDriverFiltration P hd W₂ hm₂))

/-- All initial fields of the source-data statement are discharged from the
box mean. Only the separately named dynamics assertion remains as input. -/
theorem firstContactK2SourceDataStatement_of_dynamics
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) (hdyn : FirstContactK2DynamicsStatement.{u}) :
    FirstContactK2SourceDataStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨D₁, D₂⟩ := hdyn κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  exact ⟨fck2SourceData_of_boxMean_and_dynamics h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂
      hd hζ₁ hζ₂ hae hu₀ hβ hsort hmean W₁ hm₁ hc₁ hz₁ D₁,
    fck2SourceData_of_boxMean_and_dynamics h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂
      hd hζ₁ hζ₂ hae hu₀ hβ hsort hmean W₂ hm₂ hc₂ hz₂ D₂⟩

/-- Determination with only the source dynamics gap still explicit. The initial
Gaussian law and finite force splitting are supplied by the source theorems
proved here; the other premises are the committed Theorem 1.5 reductions. -/
theorem firstContactCanonCondDetStatement_of_dynamics_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u}) (hdyn : FirstContactK2DynamicsStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_sourceData_thm12_thm13_lemma76 h12 h13 h12₀ h13₀ h76
    (firstContactK2SourceDataStatement_of_dynamics (lemma75Statement_of_thm12_thm13 h12 h13)
      (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76)
      firstContact_retainedRangeEntranceStatement hdyn)

end InteractingSLE.Restart.FCPlumb
