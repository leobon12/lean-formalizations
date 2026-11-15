/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPartWord
import InteractingSLE.Spec.Supplement.AStopPartEvent

/-!
# Theorem 1.5's leaf 3: item 1 of `AStopSourceInputs` — the type partition of the ordinary pairs

Packet PROVE-T15-ASTOP-PART. With the binders of `RLC.OrdModel.RetOrdAStopSourceSndStatement` (and of the seeded
`RLC.RetOrdAStopSourceFstSeedStatement`, which has the same binders): finitely many events `M i` of the retained
σ-algebra `retSigma76` such that

* they cover the ordinary retained pairs almost surely;
* almost surely each lies in the ordinary pairs (so every pathwise input that holds almost surely at an ordinary pair
  holds almost surely on `M i`; the parts are cut by `exists_retSigma76_ordEvent`);
* on each, the chart word has one force type at every point: `β.1` for the angle `θ₂` (second continuation), and the
  seeded word `shiftW β.2 β.1` for the angle `θ₁` (first continuation; almost surely on `M i` this is
  `shiftW (tipPos d η₁) β.1`, the word of `RetOrdAStopSourceFstStatement`).

These are the conjuncts `∃ a`, `MeasurableSet[𝓗 0] M`, `∀ᵐ ω ∂P, ω ∈ M → c ω ∈ typeSet …` of `AStopSourceInputs` and the
cover clause of the two source statements, for any filtration with `retSigma76 ≤ 𝓗 0`:

* **`exists_ordTypePartition_snd`**, **`exists_ordTypePartition_fst`**.

For Theorem 1.5; uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

namespace AStopPart

open Supp7 Restart Restart.RetAux79 Sec7 Sec7.Lemma76F
open Exist.StagedLaw.BoundaryWord (shiftW)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Cutting a cover of the ordinary pairs by a retained version of the ordinary event.** -/
theorem exists_ordPartition_of_cover (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) (u₀ : ℂ → ℝ)
    (a r : ℝ≥0) {n : ℕ} {M : Fin n → Set Ω} (hMm : ∀ i, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ a r] (M i))
    (hcover : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) a (η₂ ω) (ζ₂ ω) r → ∃ i, ω ∈ M i) :
    ∃ M' : Fin n → Set Ω, (∀ i, M' i ⊆ M i) ∧ (∀ i, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ a r] (M' i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) a (η₂ ω) (ζ₂ ω) r → ∃ i, ω ∈ M' i) ∧
      ∀ i, ∀ᵐ ω ∂P, ω ∈ M' i → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) a (η₂ ω) (ζ₂ ω) r := by
  obtain ⟨B, hBm, hB⟩ := exists_retSigma76_ordEvent hL75 hκ hκ4 hb hh hη₁ hη₂ u₀ a r
  refine ⟨fun i => M i ∩ B, fun i => inter_subset_left, fun i => (hMm i).inter hBm, ?_, fun i => ?_⟩
  · filter_upwards [hcover, hB] with ω hc hBω hp
    obtain ⟨i, hi⟩ := hc hp
    exact ⟨i, hi, hBω.2 hp⟩
  · filter_upwards [hB] with ω hBω hω
    exact hBω.1 hω.2

/-- **Item 1 of `AStopSourceInputs` for the second continuation**: with the binders of
`RLC.OrdModel.RetOrdAStopSourceSndStatement`, finitely many `retSigma76` events cover the ordinary pairs almost surely,
lie almost surely in them, and carry one force type of `β.1` for the angle `θ₂` at every point. -/
theorem exists_ordTypePartition_snd (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord × ℝ}
    (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1))
    (hword : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
      IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
      IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) :
    ∃ (n : ℕ) (a : Fin n → ForceWordType) (M : Fin n → Set Ω),
      (∀ i, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (M i)) ∧ (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      (∀ i, ∀ᵐ ω ∂P, ω ∈ M i → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) ∧
      ∀ i, ∀ ω ∈ M i, (β ω).1 ∈ FCDet.typeSet κ θ₂ (a i).nL (a i).nR (a i).rhoL (a i).rhoR := by
  obtain ⟨n, a, M, hMm, hcover, htype⟩ :=
    exists_ordTypeCover_snd hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hβ hmean hword
  obtain ⟨M', hM'M, hM'm, hcover', hord⟩ :=
    exists_ordPartition_of_cover hL75 hκ hκ4 hb hh hη₁ hη₂ u₀ d.u d.r hMm hcover
  exact ⟨n, a, M', hM'm, fun i => retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r _ (hM'm i), hcover', hord,
    fun i ω hω => htype i ω (hM'M i hω)⟩

/-- **Item 1 of `AStopSourceInputs` for the first continuation**: with the binders of
`RLC.RetOrdAStopSourceFstSeedStatement` (the same as those of `RLC.OrdModel.RetOrdAStopSourceFstStatement`), finitely
many `retSigma76` events cover the ordinary pairs almost surely, lie almost surely in them, and carry one force type of
the seeded word `shiftW β.2 β.1` for the angle `θ₁` at every point; almost surely on each part this is the word
`shiftW (tipPos d η₁) β.1`. -/
theorem exists_ordTypePartition_fst (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord × ℝ}
    (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1))
    (hword : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
      IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
      IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) :
    ∃ (n : ℕ) (a : Fin n → ForceWordType) (M : Fin n → Set Ω),
      (∀ i, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (M i)) ∧ (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      (∀ i, ∀ᵐ ω ∂P, ω ∈ M i → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) ∧
      (∀ i, ∀ ω ∈ M i, shiftW (β ω).2 (β ω).1 ∈ FCDet.typeSet κ θ₁ (a i).nL (a i).nR (a i).rhoL (a i).rhoR) ∧
      ∀ i, ∀ᵐ ω ∂P, ω ∈ M i →
        shiftW (tipPos d η₁ ω) (β ω).1 ∈ FCDet.typeSet κ θ₁ (a i).nL (a i).nR (a i).rhoL (a i).rhoR := by
  obtain ⟨n, a, M, hMm, hcover, htype, -⟩ :=
    exists_ordTypeCover_fst hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hβ hmean hword
  obtain ⟨M', hM'M, hM'm, hcover', hord⟩ :=
    exists_ordPartition_of_cover hL75 hκ hκ4 hb hh hη₁ hη₂ u₀ d.u d.r hMm hcover
  refine ⟨n, a, M', hM'm, fun i => retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r _ (hM'm i), hcover', hord,
    fun i ω hω => htype i ω (hM'M i hω), fun i => ?_⟩
  filter_upwards [hord i, hword] with ω hoω hω hi
  rw [← (hω (hoω hi)).2.1]
  exact htype i ω (hM'M i hi)

end AStopPart

end RLC

end InteractingSLE
