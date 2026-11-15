/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdModelCtor
import InteractingSLE.Spec.Supplement.OrdAStopLeaf

/-!
# The A-stopped model statements from source inputs

Packet PROVE-T15-ASTOP2. PROVE-T15-ASTOP reduced Theorem 1.5's leaf 3 to two model statements,
`RLC.RetOrdStoppedModelsSndStatement` and `RLC.RetOrdStoppedModelsFstStatement` (finitely many type events covering
the ordinary pairs, each with an A-stopped model with an initial code, `OrdAStop.StoppedModelTransferJ`). With the
constructor `nonempty_stoppedModelTransferJ_of_aStop` every model-side requirement (carrier, image filtration, law
transports, the A-stop announcement with the code of `I_A`, the original end through the frozen threshold, the K2
sequences) is discharged; what remains is a statement about the source alone:

* `AStopSourceInputs κ θ P M Sd c Hc V γ`: on the event `M`, a filtration `𝓗`, a force type, an adapted continuous
  driver, the chart end points `E` of the A-set and the seed `Sd` (both initial), versions `V'`, `γ'` of the stop
  and the path (a.s. equal to
  `V`, `γ` on `M`), the typed stopped-K2 laws (S), (L), integrable pairings, and the pathwise A-stop facts
  (generation, `0 < V' ≤ thr`, no earlier contact with `aStopSet E`, a finite stop is the threshold or a contact);
* **`nonempty_stoppedModelTransferJ_of_sourceInputs`**: these inputs give the model;
* `RetOrdAStopSourceSndStatement`, `RetOrdAStopSourceFstStatement` (named source statements, **not proved**: the
  RETPLUMB-scale construction of the A-stopped continuation's processes, see the handoff) and
  **`retOrdStoppedModelsSndStatement_of_source`**, **`retOrdStoppedModelsFstStatement_of_source`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdModel

open LQGMetric (DistOn TestOn)
open Restart Restart.RetAux79 Sec7.PocketTraversal Restart.DomainMarkov Restart.DomainMarkov.K2
  Restart.FCDet OrdAStop

universe u v

section Source

variable {Ω : Type v} [mΩ : MeasurableSpace Ω]

/-- **The source inputs of an A-stopped model** on an event `M` (see the module docstring). -/
def AStopSourceInputs (κ θ : ℝ) (P : Measure Ω) (M : Set Ω) (Sd : Ω → ℝ) (c : Ω → BoundaryWord)
    (Hc : Ω → DistOn upperHalfPlaneOpens) (V : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) : Prop :=
  ∃ (a : ForceWordType) (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (E : Ω → Ends) (V' : Ω → ℝ≥0∞)
    (γ' : Ω → ℝ≥0 → ℂ),
    MeasurableSet[𝓗 0] M ∧ Measurable[𝓗 0] c ∧ Measurable Hc ∧
    (∀ ω, Continuous (W · ω)) ∧ (∀ ω, W 0 ω = 0) ∧ StronglyAdapted 𝓗 W ∧
    (∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V' ω ≤ t}) ∧
    (∀ t, Measurable fun ω => γ' ω t) ∧ (∀ ω, ContinuousOn (γ' ω) {t | (t : ℝ≥0∞) ≤ V' ω}) ∧
    (∀ ω, γ' ω 0 = 0) ∧ Measurable[𝓗 0] E ∧ Measurable[𝓗 0] Sd ∧
    (∀ᵐ ω ∂P, ω ∈ M → V' ω = V ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ' ω t = γ ω t) ∧
    (∀ᵐ ω ∂P, ω ∈ M → c ω ∈ typeSet κ θ a.nL a.nR a.rhoL a.rhoR) ∧
    (∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω) φ) (P.restrict M)) ∧
    HasSafeLaw κ a.rhoL a.rhoR P 𝓗 M V' W
      (geomLW W fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω))
      (geomRW W fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω))
      (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω)) ∧
    HasSafeMembers P 𝓗 M V' W (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω)) ∧
    (∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (V' ω) (γ' ω)) ∧
    (∀ᵐ ω ∂P, ω ∈ M → 0 < V' ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → V' ω ≤ thr a.rhoL a.rhoR W
      (fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) (fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) ω) ∧
    (∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V' ω → γ' ω t ∉ aStopSet (E ω)) ∧
    (∀ᵐ ω ∂P, ω ∈ M → V' ω ≠ ⊤ → V' ω = thr a.rhoL a.rhoR W
      (fun ω => typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) (fun ω => typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) ω ∨
        γ' ω (V' ω).toNNReal ∈ aStopSet (E ω))

/-- A model of a version of the stop and the path is a model of the stop and the path. -/
def congrTransferJ {κ θ : ℝ} {P : Measure Ω} {F : Set Ω} {c : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {V V' : Ω → ℝ≥0∞} {γ γ' : Ω → ℝ≥0 → ℂ}
    (T : StoppedModelTransferJ κ θ P F c Hc V' γ')
    (h : ∀ᵐ ω ∂P, ω ∈ F → V' ω = V ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ' ω t = γ ω t) :
    StoppedModelTransferJ κ θ P F c Hc V γ :=
  { T with
    agrees := by
      filter_upwards [T.agrees, h] with ω h1 h2 hω
      obtain ⟨ec, eH, eV, eγ⟩ := h1 hω
      obtain ⟨eV', eγ'⟩ := h2 hω
      refine ⟨ec, eH, eV.trans eV', fun t ht => ?_⟩
      rw [eγ t (eV'.symm ▸ ht), eγ' t ht] }

/-- **The A-stopped model from source inputs.** -/
theorem nonempty_stoppedModelTransferJ_of_sourceInputs {κ θ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {M : Set Ω} {c : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞}
    {γ : Ω → ℝ≥0 → ℂ} {Sd : Ω → ℝ} (h : AStopSourceInputs κ θ P M Sd c Hc V γ) (hPM : P M ≠ 0) :
    Nonempty (StoppedModelTransferJ κ θ P M c Hc V γ) := by
  obtain ⟨a, 𝓗, W, E, V', γ', hM, hc, hHc, hWc, hW0, hWa, hVs, hγm, hγc, hγ0, hE, hSd, hag, htype, hint, hS,
    hL, hg, hVpos, hthr, hoff, hend⟩ := h
  obtain ⟨T⟩ := nonempty_stoppedModelTransferJ_of_aStop a hM hPM hc hHc hWc hW0 hWa hVs hγm hγc hγ0 hE hSd
    htype hint hS hL hg hVpos hthr hoff hend
  exact ⟨congrTransferJ T hag⟩

end Source

/-! ### The two continuations -/

open Supp7 Supp9D Sec7.Lemma76F

/-- **Source inputs of the A-stopped second continuation** (the remaining construction for
`RLC.RetOrdStoppedModelsSndStatement`): with its binders, finitely many measurable events cover the ordinary pairs
almost surely, and on each with positive probability the second continuation of `d`'s chart, stopped at its first new
contact with `η₁[0,u] ∪ η₂[0,r]`, has A-stopped source inputs with word `β.1` and the retained chart field.
**Not proved in Lean.** -/
def RetOrdAStopSourceSndStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∃ (n : ℕ) (M : Fin n → Set Ω), (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, P (M i) ≠ 0 → AStopSourceInputs κ θ₂ P (M i) (fun _ => 0) (fun ω => (β ω).1) (hd.chartField κ h)
        (fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
        (fun ω => canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)

/-- **`RetOrdStoppedModelsSndStatement` from source inputs.** -/
theorem retOrdStoppedModelsSndStatement_of_source (hsrc : RetOrdAStopSourceSndStatement.{u}) :
    RetOrdStoppedModelsSndStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
  obtain ⟨n, M, hM, hcover, hsource⟩ := hsrc κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hag u₀ hu₀ β hβ hmean hword
  exact ⟨n, M, hM, hcover, fun i hi => nonempty_stoppedModelTransferJ_of_sourceInputs (hsource i hi) hi⟩

/-- **Source inputs of the A-stopped first continuation in the chart recentred at the first tip** (the remaining
construction for `RLC.RetOrdStoppedModelsFstStatement`). **Not proved in Lean.** -/
def RetOrdAStopSourceFstStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∃ (n : ℕ) (M : Fin n → Set Ω), (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, P (M i) ≠ 0 → AStopSourceInputs κ θ₁ P (M i) (fun _ => 0)
        (fun ω => Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β ω).1)
        (fun ω => Exist.flowField (tipPos d η₁ ω) 0 (hd.chartField κ h ω))
        (fun ω => canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
        (fun ω => canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)

/-- **`RetOrdStoppedModelsFstStatement` from source inputs.** -/
theorem retOrdStoppedModelsFstStatement_of_source (hsrc : RetOrdAStopSourceFstStatement.{u}) :
    RetOrdStoppedModelsFstStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
  obtain ⟨n, M, hM, hcover, hsource⟩ := hsrc κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hag u₀ hu₀ β hβ hmean hword
  exact ⟨n, M, hM, hcover, fun i hi => nonempty_stoppedModelTransferJ_of_sourceInputs (hsource i hi) hi⟩

end InteractingSLE.RLC.OrdModel
