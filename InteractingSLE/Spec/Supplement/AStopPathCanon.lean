/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathTermWire

/-!
# Item 6 in canonical form (the form PROVE-T15-ASTOP-SAFE consumes)

Packet PROVE-T15-ASTOP-PATH. `AStopPathCanonSndStatement` / `AStopPathCanonFstStatement` are verbatim copies of
PROVE-T15-ASTOP-SAFE's named inputs `AStopSafe.AStopPathSndStatement` / `AStopSafe.AStopPathFstStatement` (item 6 of
`AStopSourceInputs` for the canonical A-stopped life and path, any continuous driver generating them, the real chart
points over `A` as the stop set). Both are **proved** here, the first outright and the second from Lemma 7.5 (for the
sided word at the first tip, PROVE-T15-ORDDET3's `ae_isRetainedWordFst_of_meanIdent`):
**`aStopPathCanonSndStatement`**, **`aStopPathCanonFstStatement_of_lemma75`**. (The two definitions are the same terms
as SAFE's, so `Iff.rfl` / `id` transfers them.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
namespace InteractingSLE.RLC.AStopPath

open Exist.StagedLaw.BoundaryWord (shiftW)

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F AStopProc OrdModel FCDet

universe u

/-- **Item 6 for the second continuation, canonical form** (verbatim copy of `AStopSafe.AStopPathSndStatement`). -/
def AStopPathCanonSndStatement : Prop :=
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
    ∀ (a : ForceWordType) (M : Set Ω),
      (∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) →
      (∀ ω ∈ M, (β ω).1 ∈ typeSet κ θ₂ a.nL a.nR a.rhoL a.rhoR) →
    ∀ W : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (W · ω)) → (∀ ω, W 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω)
        (canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
        (canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)) →
      (∀ᵐ ω ∂P, ω ∈ M →
        0 < canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0) ∧
      (∀ᵐ ω ∂P, ω ∈ M →
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≤
          thr a.rhoL a.rhoR W (fun ω => typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1)
            (fun ω => typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1) ω) ∧
      (∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞) < canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
        canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 t ∉
          {z : ℂ | z.im = 0 ∧ d.inv ω z ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r}) ∧
      (∀ᵐ ω ∂P, ω ∈ M →
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≠ ⊤ →
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 =
            thr a.rhoL a.rhoR W (fun ω => typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1)
              (fun ω => typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1) ω ∨
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0
              (canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
                (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0).toNNReal ∈
            {z : ℂ | z.im = 0 ∧ d.inv ω z ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r})

/-- **Item 6 for the first continuation at its seed, canonical form** (verbatim copy of
`AStopSafe.AStopPathFstStatement`). -/
def AStopPathCanonFstStatement : Prop :=
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
    ∀ (a : ForceWordType) (M : Set Ω),
      (∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) →
      (∀ ω ∈ M, shiftW (β ω).2 (β ω).1 ∈ typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR) →
    ∀ W : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous (W · ω)) → (∀ ω, W 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω)
        (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω))
        (fun t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
          (tipPos d η₁ ω) t - (β ω).2)) →
      (∀ᵐ ω ∂P, ω ∈ M → 0 < canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ M → canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) ≤
        thr a.rhoL a.rhoR W (fun ω => typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1))
          (fun ω => typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1)) ω) ∧
      (∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) →
        canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
            (tipPos d η₁ ω) t - (β ω).2 ∉
          {z : ℂ | z.im = 0 ∧ d.inv ω (z + (β ω).2) ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r}) ∧
      (∀ᵐ ω ∂P, ω ∈ M → canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) ≠ ⊤ →
        canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
            (tipPos d η₁ ω) =
          thr a.rhoL a.rhoR W (fun ω => typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1))
            (fun ω => typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1)) ω ∨
        canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω)
            (canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
              (tipPos d η₁ ω)).toNNReal - (β ω).2 ∈
          {z : ℂ | z.im = 0 ∧ d.inv ω (z + (β ω).2) ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r})


/-- **Item 6 for the second continuation, canonical form, proved.** -/
theorem aStopPathCanonSndStatement : AStopPathCanonSndStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
    a M hMord htype W hWc hW0 hgen
  have htype' : ∀ᵐ ω ∂P, ω ∈ M → (β ω).1 ∈ typeSet κ θ₂ a.nL a.nR a.rhoL a.rhoR :=
    Eventually.of_forall fun ω hω => htype ω hω
  obtain ⟨hpos, hthr, havoid, hend⟩ := ae_aStopPath_snd hκ hκ4 hb hx hh hη₁ hη₂ hd hag hword hMord htype' hWc hW0
    (V' := fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
    (γ' := fun ω => canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
    (J := fun ω => {z : ℂ | z.im = 0 ∧ d.inv ω z ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r})
    (Eventually.of_forall fun _ _ => ⟨rfl, fun _ _ => rfl⟩) hgen (Eventually.of_forall fun _ _ => rfl)
  have hT := aStopTerminalSndStatement κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
    (fun ω => (β ω).1) (hword.mono fun ω hω ho => ⟨(hω ho).2.2.2.1, (hω ho).2.2.2.2⟩)
  refine ⟨hpos, hthr, havoid, ?_⟩
  filter_upwards [hend, hT, hgen, hMord, hthr] with ω h1 h2 h4 h5 h6 hω hfin
  rcases h1 hω hfin with ⟨hstop, hoff⟩ | h1
  · left
    have hth := h2 (h5 hω) hstop hoff (W · ω) (hWc ω) (hW0 ω) (h4 hω) hfin _ _ _ _ (htype ω hω)
    refine le_antisymm (h6 hω) ?_
    have hle := FCPlumb.thr_le_of_force_threshold hWc (ω := ω) (ρL := a.rhoL) (ρR := a.rhoR)
      (xL := fun ω => typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1)
      (xR := fun ω => typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω).1) hth
    rwa [ENNReal.coe_toNNReal hfin] at hle
  · exact Or.inr h1

/-- **Item 6 for the first continuation at its seed, canonical form, proved from Lemma 7.5.** -/
theorem aStopPathCanonFstStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) :
    AStopPathCanonFstStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
    a M hMord htype W hWc hW0 hgen
  have htype' : ∀ᵐ ω ∂P, ω ∈ M → shiftW (β ω).2 (β ω).1 ∈ typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR :=
    Eventually.of_forall fun ω hω => htype ω hω
  have hτ : ∀ᵐ ω ∂P, ω ∈ M → (β ω).2 = tipPos d η₁ ω := by
    filter_upwards [hMord, hword] with ω h1 h2 hω using (h2 (h1 hω)).2.1
  have hsided := ae_isRetainedWordFst_of_meanIdent hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hmean
    (hword.mono fun ω hω ho => ⟨(hω ho).1, (hω ho).2.2.2.1⟩)
  have hfst : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      IsRetainedWordFst κ θ₁ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (tipPos d η₁ ω) (β ω).1 ∧
      IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1 := by
    filter_upwards [hsided, hword] with ω h1 h2 ho using ⟨h1 ho, (h2 ho).2.2.2.2⟩
  obtain ⟨hpos, hthr, havoid, hend⟩ := ae_aStopPath_fst hκ hκ4 hb hx hh hη₁ hη₂ hd hag hfst hMord hτ htype' hWc hW0
    (V' := fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
      (tipPos d η₁ ω))
    (γ' := fun ω t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
      (tipPos d η₁ ω) t - (β ω).2)
    (J := fun ω => {z : ℂ | z.im = 0 ∧ d.inv ω (z + (β ω).2) ∈ η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r})
    (Eventually.of_forall fun _ _ => ⟨rfl, fun _ _ => rfl⟩) hgen (Eventually.of_forall fun _ _ => rfl)
  have hT := aStopTerminalFstStatement κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
    (fun ω => (β ω).1) hfst
  refine ⟨hpos, hthr, havoid, ?_⟩
  filter_upwards [hend, hT, hgen, hMord, hthr, hτ] with ω h1 h2 h4 h5 h6 h7 hω hfin
  rcases h1 hω hfin with ⟨hstop, hoff⟩ | h1
  · left
    have hτe := h7 hω
    have hg := h4 hω
    have hg' := isGeneratingTrace_congr_le (η' := fun t => canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u
      (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) t - tipPos d η₁ ω) hg
      fun t _ => by rw [hτe]
    have htyp := htype ω hω
    rw [hτe] at htyp
    have hth := h2 (h5 hω) hstop hoff (W · ω) (hWc ω) (hW0 ω) hg' hfin _ _ _ _ htyp
    set V := canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
      (tipPos d η₁ ω) with hVdef
    rw [← hτe] at hth
    refine le_antisymm (h6 hω) ?_
    have hle := FCPlumb.thr_le_of_force_threshold hWc (ω := ω) (T := V.toNNReal) (ρL := a.rhoL) (ρR := a.rhoR)
      (xL := fun ω => typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1))
      (xR := fun ω => typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (β ω).2 (β ω).1)) hth
    rwa [ENNReal.coe_toNNReal hfin] at hle
  · exact Or.inr h1

end InteractingSLE.RLC.AStopPath
