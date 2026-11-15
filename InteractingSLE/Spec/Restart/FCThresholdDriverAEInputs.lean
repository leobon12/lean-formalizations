/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCThresholdDriverAE

/-!
# The remaining K2 fields after measurable driver reconstruction

Driver existence, coordinate measurability, continuous zero-start versions and
actual generating traces are proved in `FCThresholdDriverAE`. The data below
isolate the remaining stochastic and force-word mathematics. An almost-sure
branch cover is sufficient; no cover of exceptional word values is required.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

open DomainMarkov.K2 LocalSets

universe u

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The retained past joined with the driver history, completed inside the
ambient sigma algebra. This is a concrete filtration on the source space. -/
def fcRetainedDriverFiltration (P : Measure Ω) {d : PairData Ω} (hd : d.IsMeasGood)
    (W : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (W t)) : Filtration ℝ≥0 mΩ where
  seq t := mΩ ⊓ aeSigma (fcDriverFiltration (retHist d) W hd.measurable_retHist hm t) P
  mono' _s _t hst := inf_le_inf_left mΩ (StagedEntrance.aeSigma_le_aeSigma
    (((fcDriverFiltration (retHist d) W hd.measurable_retHist hm).mono hst).trans (le_aeSigma _ P)))
  le' _ := inf_le_left

/-- The concrete filtration retains the entire completed first-contact past. -/
theorem retSigma_le_fcRetainedDriverFiltration (P : Measure Ω) {d : PairData Ω}
    (hd : d.IsMeasGood) (W : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (W t)) (t : ℝ≥0) :
    retSigma d P ≤ fcRetainedDriverFiltration P hd W hm t := by
  apply inf_le_inf_left mΩ
  exact StagedEntrance.aeSigma_le_aeSigma
    ((fcDriverFiltration_word_le (retHist d) W hd.measurable_retHist hm t).trans (le_aeSigma _ P))

/-- The actual measurable driver is strongly adapted to this concrete filtration. -/
theorem stronglyAdapted_fcRetainedDriverFiltration (P : Measure Ω) {d : PairData Ω}
    (hd : d.IsMeasGood) (W : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (W t)) :
    StronglyAdapted (fcRetainedDriverFiltration P hd W hm) W := by
  intro t
  exact ((fcDriverFiltration_adapted (retHist d) W hd.measurable_retHist hm).2 t).mono
    (le_inf ((fcDriverFiltration (retHist d) W hd.measurable_retHist hm).le t) (le_aeSigma _ P))

/-- Explicit remaining K2/force-word data for an already constructed actual driver.
These fields are not asserted to follow from the source hypotheses in this file. -/
structure FCAEK2Inputs (P : Measure Ω) (κ θ : ℝ) (M : Set Ω)
    (β : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (U : Ω → ℝ≥0∞) (driver : ℝ≥0 → Ω → ℝ) (filtration : Filtration ℝ≥0 mΩ) where
  branch : ℕ → Set Ω
  branch_measurable : ∀ i, MeasurableSet[filtration 0] (branch i)
  cover_ae : ∀ᵐ ω ∂P, ω ∈ M → ∃ i, ω ∈ branch i
  nL : ℕ → ℕ
  nR : ℕ → ℕ
  rhoL : ∀ i, Fin (nL i) → ℝ
  rhoR : ∀ i, Fin (nR i) → ℝ
  word_type : ∀ i ω, ω ∈ branch i → β ω ∈ FCDet.typeSet κ θ (nL i) (nR i) (rhoL i) (rhoR i)
  integrable : ∀ i (φ : TestOn upperHalfPlaneOpens),
    Integrable (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ) (P.restrict (branch i))
  seed : ∀ i, ∀ᵐ ω ∂P, ω ∈ branch i →
    ¬ ForceWord.ThresholdCondition (rhoL i) (rhoR i) 0
      (FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
      (FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
  safe_law : ∀ i, HasSafeLaw κ (rhoL i) (rhoR i) P filtration (branch i)
    (FCDet.thr (rhoL i) (rhoR i) driver
      (fun ω => FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
      (fun ω => FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))) driver
    (Sec7.PocketTraversal.geomLW driver
      (fun ω => FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω)))
    (Sec7.PocketTraversal.geomRW driver
      (fun ω => FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω)))
    (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  safe_members : ∀ i, HasSafeMembers P filtration (branch i)
    (FCDet.thr (rhoL i) (rhoR i) driver
      (fun ω => FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
      (fun ω => FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))) driver
    (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  lifetime : ∀ i, ∀ᵐ ω ∂P, ω ∈ branch i →
    U ω = FCDet.thr (rhoL i) (rhoR i) driver
      (fun ω => FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
      (fun ω => FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω)) ω

/-- Almost-sure branch coverage supplies the committed record on a measurable
modification of the live event. All path and continuous-driver fields are supplied
by the proved reconstruction, rather than additional fields of `FCAEK2Inputs`. -/
theorem hasAEThresholdDriverInputs_of_k2Inputs {P : Measure Ω} {κ θ : ℝ} {M : Set Ω}
    (hM : MeasurableSet M) {β : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens}
    {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (U ω) (Γ ω))
    {𝓕 : Filtration ℝ≥0 mΩ} (ha : StronglyAdapted 𝓕 W) (hβ : Measurable[𝓕 0] β)
    (h : FCAEK2Inputs P κ θ M β Hc U W 𝓕) :
    HasAEThresholdDriverInputs P κ θ M β Hc Γ U := by
  let M' : Set Ω := M ∩ ⋃ i, h.branch i
  have hM' : MeasurableSet M' := hM.inter (MeasurableSet.iUnion fun i =>
    (𝓕.le 0) _ (h.branch_measurable i))
  have he : M =ᵐ[P] M' := by
    filter_upwards [h.cover_ae] with ω hc
    apply propext
    exact ⟨fun hm => ⟨hm, mem_iUnion.2 (hc hm)⟩, fun hm => hm.1⟩
  let I : FCThresholdDriverInputs P κ θ M' β Hc Γ U := {
    filtration := 𝓕
    driver := W
    driver_zero := hW0
    driver_continuous := hWc
    driver_adapted := ha
    word_measurable := hβ
    branch := h.branch
    branch_measurable := h.branch_measurable
    cover := fun _ hm => mem_iUnion.1 hm.2
    nL := h.nL
    nR := h.nR
    rhoL := h.rhoL
    rhoR := h.rhoR
    word_type := h.word_type
    integrable := h.integrable
    seed := h.seed
    safe_law := h.safe_law
    safe_members := h.safe_members
    lifetime := h.lifetime
    generating_trace := hgen.mono fun _ hg hm => hg hm.1
    path_continuous := hgen.mono fun _ hg hm => (hg hm.1).2.1 }
  exact ⟨M', hM', he, ⟨I⟩⟩

/-- The exact remaining source-level K2 and force-word construction for the
actual measurable drivers. This proposition is not proved here. In particular the
box mean and clock do not themselves state a collision-threshold identity. -/
def FirstContactAEK2RealizationStatement : Prop :=
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
      Nonempty (FCAEK2Inputs P κ θ₁ (meetSet d) β (hd.chartField κ h) U₁ W₁
        (fcRetainedDriverFiltration P hd W₁ hm₁)) ∧
        Nonempty (FCAEK2Inputs P κ θ₂ (meetSet d) β (hd.chartField κ h) U₂ W₂
          (fcRetainedDriverFiltration P hd W₂ hm₂))

/-- The remaining K2 construction completes the almost-sure record statement;
all driver existence and generating-trace obligations are proved above. -/
theorem firstContactAEThresholdDriverInputsStatement_of_k2Realization
    (h77 : Supp10.Lemma77Statement.{u})
    (hK2 : FirstContactAEK2RealizationStatement.{u}) :
    FirstContactAEThresholdDriverInputsStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
  obtain ⟨W₁, W₂, hm₁, hm₂, hc₁, hc₂, hz₁, hz₂, hg⟩ :=
    exists_measurable_drivers_canonClock h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae
      hγ₁ hγ₂ hU₁ hU₂ hcanon
  obtain ⟨⟨I₁⟩, ⟨I₂⟩⟩ := hK2 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  have hM : MeasurableSet (meetSet d) := retSigma_le P _ (hd.measurableSet_meetSet P)
  exact ⟨hasAEThresholdDriverInputs_of_k2Inputs hM hc₁ hz₁
      (hg.mono fun _ hω hm => (hω hm).1)
      (stronglyAdapted_fcRetainedDriverFiltration P hd W₁ hm₁)
      (hβ.mono (retSigma_le_fcRetainedDriverFiltration P hd W₁ hm₁ 0) le_rfl) I₁,
    hasAEThresholdDriverInputs_of_k2Inputs hM hc₂ hz₂
      (hg.mono fun _ hω hm => (hω hm).2)
      (stronglyAdapted_fcRetainedDriverFiltration P hd W₂ hm₂)
      (hβ.mono (retSigma_le_fcRetainedDriverFiltration P hd W₂ hm₂ 0) le_rfl) I₂⟩

/-- Source-facing determination with the exact remaining hypotheses displayed.
The K2 force-word construction is still explicit; it is not asserted discharged. -/
theorem firstContactCanonCondDetStatement_of_k2Realization_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u}) (hK2 : FirstContactAEK2RealizationStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_aeThresholdInputs_thm12_thm13_lemma76 h12 h13 h12₀ h13₀ h76
    (firstContactAEThresholdDriverInputsStatement_of_k2Realization
      (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76) hK2)

end InteractingSLE.Restart.FCPlumb
