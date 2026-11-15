/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2RealizeLaws

/-!
# First-contact K2 realization from explicit source obligations

The remaining source mathematics is recorded in `FCK2SourceData`. From those
obligations we construct the committed record: finite measurable branches, seed,
integrability and safe identities at the force threshold. This does not assert
that the box mean identification proves the source obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open RetAux79 DomainMarkov.K2 LocalSets
universe u
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The canonical event for a prescribed force type. -/
def fcTypeBranch (κ θ : ℝ) (M : Set Ω) (β : Ω → BoundaryWord) (a : ForceWordType) : Set Ω :=
  M ∩ β ⁻¹' forceTypeSet κ θ a

/-- The source obligations, before branch enumeration and analytic adapters.
`bounded_types` must be established for the chosen measurable word from its mean
identification; the explicit geometrical word has the proved bound above.
`initial_gaussian` is the initial marked Gaussian law with bounded mean for each
clamped test pairing. `admissible` is Aux. 78's incident-height assertion. The safe
identities are at the canonical path lifetime `U`, not an assumed force lifetime.
`collision_lifetime` is the collision-weight/no-return equality. None of these
source assertions is claimed proved by this record declaration. -/
structure FCK2SourceData (P : Measure Ω) (κ θ : ℝ) (M : Set Ω)
    (β : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (U : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) where
  max_marks : ℕ
  weights : Finset ℝ
  bounded_types : ∀ᵐ ω ∂P, ω ∈ M → HasBoundedForceType κ θ max_marks weights (β ω)
  initial_gaussian : ∀ (a : ForceWordType) (φ : TestOn upperHalfPlaneOpens),
    ∃ (μ V : Ω → ℝ) (K C : ℝ),
      @Sec6.Prop65.IsCondGaussian Ω (𝓕 0) mΩ P
        ((fcTypeBranch κ θ M β a).indicator
          (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ)) μ V K ∧
      ∀ ω, ‖μ ω‖ ≤ C
  admissible : ∀ᵐ ω ∂P, ω ∈ M → ExplState.IsAdmissibleSeed κ
    (PiecewiseConstantBoundaryData.leftLim (β ω).fn 0)
    (PiecewiseConstantBoundaryData.rightLim (β ω).fn 0) θ
  safe_law : ∀ a : ForceWordType,
    HasSafeLaw κ a.rhoL a.rhoR P 𝓕 (fcTypeBranch κ θ M β a) U W
      (Sec7.PocketTraversal.geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
      (Sec7.PocketTraversal.geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
      (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  safe_members : HasSafeMembers P 𝓕 M U W (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  collision_lifetime : ∀ a : ForceWordType, ∀ᵐ ω ∂P, ω ∈ fcTypeBranch κ θ M β a →
    U ω = FCDet.thr a.rhoL a.rhoR W
      (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω))
      (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)) ω

/-- The complete record construction from the exact source obligations. Null
modifications of the word require no new assumptions or everywhere cover. -/
theorem fcaeK2Inputs_of_sourceData {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) {M : Set Ω} {β : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {U : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} (hM : MeasurableSet[𝓕 0] M) (hβ : Measurable[𝓕 0] β)
    (h : FCK2SourceData P κ θ M β Hc U W 𝓕) :
    Nonempty (FCAEK2Inputs P κ θ M β Hc U W 𝓕) := by
  obtain ⟨a, B, hBm, hBa, hcover⟩ := exists_ae_forceType_branches hβ hM h.bounded_types
  have hsub (i : ℕ) : B i ⊆ fcTypeBranch κ θ M β (a i) := hBa i
  have hBM (i : ℕ) : B i ⊆ M := (hBa i).trans inter_subset_left
  have hT (i : ℕ) : ∀ᵐ ω ∂P, ω ∈ B i → U ω = FCDet.thr (a i).rhoL (a i).rhoR W
      (fun ω => FCDet.typeXL κ θ (a i).nL (a i).nR (a i).rhoL (a i).rhoR (β ω))
      (fun ω => FCDet.typeXR κ θ (a i).nL (a i).nR (a i).rhoL (a i).rhoR (β ω)) ω :=
    (h.collision_lifetime (a i)).mono fun _ hω hB => hω (hsub i hB)
  refine ⟨{
    branch := B
    branch_measurable := hBm
    cover_ae := hcover
    nL := fun i => (a i).nL
    nR := fun i => (a i).nR
    rhoL := fun i => (a i).rhoL
    rhoR := fun i => (a i).rhoR
    word_type := fun i ω hω => (hBa i hω).2
    integrable := ?_
    seed := ?_
    safe_law := fun i => hasSafeLaw_of_subset_ae_lifetime (hsub i) (hT i) (h.safe_law (a i))
    safe_members := fun i => hasSafeMembers_of_subset_ae_lifetime (hBM i) (hT i) h.safe_members
    lifetime := hT }⟩
  · intro i φ
    obtain ⟨μ, V, K, C, hg, hμ⟩ := h.initial_gaussian (a i) φ
    have hm : MeasurableSet (fcTypeBranch κ θ M β (a i)) :=
      𝓕.le 0 _ (hM.inter (hβ (measurableSet_forceTypeSet κ θ (a i))))
    exact (integrable_restrict_of_condGaussian_indicator hm hg hμ).mono_measure
      (Measure.restrict_mono (hsub i) le_rfl)
  · intro i
    filter_upwards [h.admissible] with ω hω hB
    exact not_threshold_type_of_admissible hκ (hBa i hB).2 (hω (hBM i hB))


/-- The exact remaining universal source proposition. Its context is identical
 to `FirstContactAEK2RealizationStatement`; its conclusions are the explicit
 source obligations above, before the proved branch and analytic reductions.
 This proposition is a named residual hypothesis, not a source theorem. -/
def FirstContactK2SourceDataStatement : Prop :=
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
      Nonempty (FCK2SourceData P κ θ₁ (meetSet d) β (hd.chartField κ h) U₁ W₁
        (fcRetainedDriverFiltration P hd W₁ hm₁)) ∧
        Nonempty (FCK2SourceData P κ θ₂ (meetSet d) β (hd.chartField κ h) U₂ W₂
          (fcRetainedDriverFiltration P hd W₂ hm₂))

/-- The source obligations imply the requested K2 realization statement. All
record fields and both concrete source filtrations are assembled here. -/
theorem firstContactAEK2RealizationStatement_of_sourceData
    (hsource : FirstContactK2SourceDataStatement.{u}) :
    FirstContactAEK2RealizationStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨⟨I₁⟩, ⟨I₂⟩⟩ := hsource κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  exact ⟨fcaeK2Inputs_of_sourceData hκ
      (retSigma_le_fcRetainedDriverFiltration P hd W₁ hm₁ 0 _ (hd.measurableSet_meetSet P))
      (hβ.mono (retSigma_le_fcRetainedDriverFiltration P hd W₁ hm₁ 0) le_rfl) I₁,
    fcaeK2Inputs_of_sourceData hκ
      (retSigma_le_fcRetainedDriverFiltration P hd W₂ hm₂ 0 _ (hd.measurableSet_meetSet P))
      (hβ.mono (retSigma_le_fcRetainedDriverFiltration P hd W₂ hm₂ 0) le_rfl) I₂⟩

/-- Determination with the remaining source proposition visible. Theorems 1.2,
1.3 and Lemma 7.6 supply all other premises by the committed reductions. -/
theorem firstContactCanonCondDetStatement_of_sourceData_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u}) (hsource : FirstContactK2SourceDataStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_k2Realization_thm12_thm13_lemma76
    h12 h13 h12₀ h13₀ h76 (firstContactAEK2RealizationStatement_of_sourceData hsource)

end InteractingSLE.Restart.FCPlumb
