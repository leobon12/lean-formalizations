/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPartTouch
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj
import InteractingSLE.Spec.Sec7.Lemma76RIdent
import InteractingSLE.Spec.Restart.RetPlumbProofInputsWord

/-!
# Theorem 1.5's leaf 3: the type partition of the ordinary pairs (item 1 of `AStopSourceInputs`)

Packet PROVE-T15-ASTOP-PART. The A-stopped source inputs `RLC.OrdModel.AStopSourceInputs` need, on each part `M i` of a
finite measurable cover of the ordinary retained pairs, one force type for the chart word: `β.1` (second continuation,
angle `θ₂`) and its translate `shiftW (tipPos) β.1` (first continuation, angle `θ₁`). The given word `β` is arbitrary
(measurable for `retSigma76`, mean-identified and sorted at the ordinary pairs), so its length is not bounded a priori.

* **`ae_exists_boundedWord_of_meanIdent`**: almost surely at an ordinary pair, a mean-identified sorted word agrees
  off a finite set with an explicit word of length at most `3 c₀.1 + 6` and heights in the fixed palette
  `retainedHeightPalette c₀ (∓λ − θ₂χ) (∓λ − θ₁χ)` (the original heights and the four side heights): Lemma 7.6's zone
  word `wordM d` at disjoint prefixes (`Sec7.Lemma76G.isRetMeanIdent_wordM`), Aux. lemma 85's touching word `wordT d`
  at meeting prefixes (`AStopPart.isRetMeanIdentOn_wordT`). Two sorted words with the same mean pairings agree off their
  jumps (`RetAux79.word_fn_eq_of_mean_integrals`); both identify the same conditional mean (a local-set mean of the
  capped union exists, `Sec7.Lemma76F.exists_cstUnion_marked_of_isFlowLine`).
* **`exists_ordTypeCover_snd`**, **`exists_ordTypeCover_fst`**: the finite `retSigma76`-measurable type covers of the
  ordinary pairs for the two continuations, with the binders of `RLC.OrdModel.RetOrdAStopSource{Snd,Fst}Statement`.

For Theorem 1.5; uses Lemma 7.5 only (R43/R48: no Theorem 1.2/1.3 and no `*_of_param` result).
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

open Supp7 Restart Restart.RetAux79 Sec7 Sec7.Lemma76F Sec7.Lemma76G RetChart
open Exist.StagedLaw.BoundaryWord (shiftW)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **A mean-identified word agrees with a bounded explicit word off a finite set** almost surely at an ordinary pair:
Lemma 7.6's zone word of `d` if the prefixes are disjoint, Aux. lemma 85's touching word of `d` if they meet. -/
theorem ae_exists_boundedWord_of_meanIdent (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    {β : Ω → BoundaryWord}
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β)
    (hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).IsSorted) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ∃ (e : BoundaryWord) (S : Finset ℝ),
        IsBoundedWord (3 * c₀.1 + 6) (retainedHeightPalette c₀
          (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
          (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)) e ∧
        ∀ y ∉ S, (β ω).fn y = e.fn y := by
  set g₁ := -sleLambda κ - θ₂ * QuantumZipper.chiC κ with hg₁
  set g₂ := sleLambda κ - θ₂ * QuantumZipper.chiC κ with hg₂
  set g₃ := -sleLambda κ - θ₁ * QuantumZipper.chiC κ with hg₃
  set g₄ := sleLambda κ - θ₁ * QuantumZipper.chiC κ with hg₄
  -- a local-set mean of the capped union
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, -, -, e₁, e₂, g, hg, -⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hη₂
      hu₀ (capR d.u d.r) d.u d.r
  have hβ := hmean ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ e₁ e₂ hg
  -- the touching word
  obtain ⟨hTm, hTs⟩ := isRetMeanIdentOn_wordT hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hc₀ hc₀J hc₀b
  have hT := hTm ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ e₁ e₂ hg
  -- the comparison at one sample, given the explicit word's pairings
  have key : ∀ (ω : Ω) (w : BoundaryWord), (β ω).IsSorted → w.IsSorted →
      IsBoundedWord (3 * c₀.1 + 6) (retainedHeightPalette c₀ g₁ g₂ g₃ g₄) w →
      (∀ φ : TestOn upperHalfPlaneOpens, ∫ z, (β ω).mean z * φ z = ∫ z, w.mean z * φ z) →
      ∃ (e : BoundaryWord) (S : Finset ℝ), IsBoundedWord (3 * c₀.1 + 6)
        (retainedHeightPalette c₀ g₁ g₂ g₃ g₄) e ∧ ∀ y ∉ S, (β ω).fn y = e.fn y :=
    fun ω w hs hws hw he => ⟨w, (β ω).jumps ∪ w.jumps, hw, word_fn_eq_of_mean_integrals hs hws he⟩
  -- the disjoint prefixes (only possible for distinct seeds)
  have hdisj : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r) →
      ∃ (e : BoundaryWord) (S : Finset ℝ), IsBoundedWord (3 * c₀.1 + 6)
        (retainedHeightPalette c₀ g₁ g₂ g₃ g₄) e ∧ ∀ y ∉ S, (β ω).fn y = e.fn y := by
    rcases hx.lt_or_eq with hx' | hx'
    · obtain ⟨hDm, hDs⟩ := isRetMeanIdent_wordM (θ₁ := θ₁) (θ₂ := θ₂) hL75 hκ hκ4 hb hx' hh hη₁ hη₂ hd hag hu₀
        hc₀ hc₀J hc₀b
      have hD := hDm ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ e₁ e₂ hg
      filter_upwards [hβ, hD, hDs, hsort] with ω hβω hDω hDsω hsω hord hdis
      have hp := isDisjointPair_of_ordinary hord hdis
      exact key ω _ (hsω hord) (hDsω hp) (isBoundedWord_wordM d c₀ g₁ g₂ g₃ g₄ ω)
        fun φ => (hβω hord φ).symm.trans (hDω hp φ)
    · filter_upwards [ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
        ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hp₁ hp₂ _ hdis
      refine absurd (Set.disjoint_left.1 hdis ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩ ⟨0, ⟨le_rfl, zero_le⟩, ?_⟩) id
      rw [Sec7.IsPathGood.zero hp₁, Sec7.IsPathGood.zero hp₂, hx']
  filter_upwards [hβ, hT, hTs, hsort, hdisj] with ω hβω hTω hTsω hsω hdisω hord
  by_cases hdis : Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)
  · exact hdisω hord hdis
  · exact key ω _ (hsω hord) (hTsω hord hdis) (isBoundedWord_wordT d c₀ g₁ g₂ g₃ g₄ ω)
      fun φ => (hβω hord φ).symm.trans (hTω ⟨hord, hdis⟩ φ)

/-- **The type partition of the ordinary pairs for the second continuation** (item 1 of
`RLC.OrdModel.RetOrdAStopSourceSndStatement`): with the binders of that statement, finitely many events of the retained
σ-algebra `retSigma76` cover the ordinary pairs almost surely, and on each the chart word `β.1` has one force type for
the angle `θ₂` at every point. -/
theorem exists_ordTypeCover_snd (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
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
      (∀ i, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, ∀ ω ∈ M i, (β ω).1 ∈ FCDet.typeSet κ θ₂ (a i).nL (a i).nR (a i).rhoL (a i).rhoR := by
  obtain ⟨c₀, hc₀, hc₀J, hc₀b⟩ := Restart.BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).1.IsSorted := by
    filter_upwards [hword] with ω hω hord using (hω hord).1
  exact exists_typeCover (mΩ := mΩ) (m := retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) (P := P) hβ.fst
    (ae_exists_boundedWord_of_meanIdent (β := fun ω => (β ω).1) hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hc₀
      hc₀J hc₀b hmean hsort)

/-- **The type partition of the ordinary pairs for the first continuation** (item 1 of
`RLC.OrdModel.RetOrdAStopSourceFstStatement`): with the binders of that statement, finitely many events of `retSigma76`
cover the ordinary pairs almost surely; on each, the word translated by the seed, `shiftW β.2 β.1`, has one force type
for the angle `θ₁` at every point, and almost surely at an ordinary pair this is the word translated by the first tip's
chart position, `shiftW (tipPos d η₁) β.1`. -/
theorem exists_ordTypeCover_fst (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
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
      (∀ i, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      (∀ i, ∀ ω ∈ M i, shiftW (β ω).2 (β ω).1 ∈ FCDet.typeSet κ θ₁ (a i).nL (a i).nR (a i).rhoL (a i).rhoR) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∀ i, ω ∈ M i →
        shiftW (tipPos d η₁ ω) (β ω).1 ∈ FCDet.typeSet κ θ₁ (a i).nL (a i).nR (a i).rhoL (a i).rhoR := by
  obtain ⟨c₀, hc₀, hc₀J, hc₀b⟩ := Restart.BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).1.IsSorted := by
    filter_upwards [hword] with ω hω hord using (hω hord).1
  obtain ⟨n, a, M, hMm, hcover, htype⟩ :=
    exists_typeCover_shiftW (mΩ := mΩ) (m := retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) (P := P) (κ := κ) (θ := θ₁)
      hβ.fst hβ.snd
      (ae_exists_boundedWord_of_meanIdent (β := fun ω => (β ω).1) hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hag hu₀ hc₀
        hc₀J hc₀b hmean hsort)
  refine ⟨n, a, M, hMm, hcover, htype, ?_⟩
  filter_upwards [hword] with ω hω hord i hi
  rw [← (hω hord).2.1]
  exact htype i ω hi

end AStopPart

end RLC

end InteractingSLE
