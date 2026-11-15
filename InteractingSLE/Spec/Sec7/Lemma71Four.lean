/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop55Half
import InteractingSLE.Spec.Coupling.WholeField9Entr

/-!
# Lemma 7.1 with two middle curves: the four-curve space

Packet PROVE-PROP74 (specification p. 243, before Proposition 7.4: "Applying the same component-pair construction
simultaneously to finitely many middle flow lines proves the following monotonicity statement"; §7.1 setup, p. 221).
The §7.1 setup takes a GFF `h` on `ℍ` with the data of Figure 7.1 (`−A` on `ℝ₋`, `B` on `ℝ₊`), `A, B` large enough
that Proposition 5.5 applies, two outer flow lines and the middle flow line. For Proposition 7.4 there are **two**
middle flow lines: outer angles `α₁ < α₂`, middle angles `α₁ < θ₁ < θ₂ < α₂`, the curves `β = η_{α₂}` (left flank),
`γ₂ = η_{θ₂}`, `γ₁ = η_{θ₁}`, `α = η_{α₁}` (right flank).

* `IsFourCurveSpace`: the configuration — the GFF, its bounded harmonic extension, the centred zero-boundary field,
  the four flow lines with Lemma 6.2's hypotheses for the centred field, almost surely complete simple proper curves
  from `0` off `ℝ ∖ {0}` (`Prop55Half.IsSeedProper`) in the closed-side order `β ≤ γ₂ ≤ γ₁ ≤ α` (all six pairs);
* **`exists_isFourCurveSpace`**: it exists, from the non-boundary (§4.2) inputs only (ruling R43): the §4.2 reference
  (`Lemma71H.Cond44ReferenceStatement`) and Proposition 5.5 in `ℍ` (`Lemma71H.Prop55HalfPlaneStatement`); Aux. lemma
  56 at first entrance times is proved (`WholeField.retainedRangeEntranceStatement`). It generalizes
  `Lemma71H.exists_threeCurveSpace_nb` / `exists_threeCurveSpace_ordered` (one middle curve) to two middle curves;
  `exists_flowLine_lemma62` is its per-angle step (any number of middle curves).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec7.Lemma71Four

open Sec5.Prop55Half

/-- **The four-curve space** (§7.1 setup with two middle curves): a GFF `h` with the data of Figure 7.1 (`−A` on `ℝ₋`,
`B` on `ℝ₊`), its bounded harmonic extension `u₀`, the centred zero-boundary field, and four flow lines of `h` from
`0`: `β = η_{α₂}`, `γ₂ = η_{θ₂}`, `γ₁ = η_{θ₁}`, `α = η_{α₁}`, each with Lemma 6.2's hypotheses for the centred
field; almost surely all four have infinite lifetimes, are simple proper curves from `0` off `ℝ ∖ {0}`, and lie in
the closed-side order `β ≤ γ₂ ≤ γ₁ ≤ α` (each range in the closed left side of every curve to its right). -/
def IsFourCurveSpace (κ α₁ θ₁ θ₂ α₂ A B : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β γ₂ γ₁ α : Ω → ℝ≥0 → ℂ)
    (ζβ ζ₂ ζ₁ ζα : Ω → ℝ≥0∞) : Prop :=
  IsGFFWithBoundaryData P h (prop74Data A B) ((({0} : Finset ℝ)) : Set ℝ) ∧
    IsBoundedHarmonicExtension (prop74Data A B) ((({0} : Finset ℝ)) : Set ℝ) u₀ ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
    IsFlowLine κ (prop74Data A B) {0} 0 α₂ P h β ζβ ∧ IsFlowLine κ (prop74Data A B) {0} 0 θ₂ P h γ₂ ζ₂ ∧
    IsFlowLine κ (prop74Data A B) {0} 0 θ₁ P h γ₁ ζ₁ ∧ IsFlowLine κ (prop74Data A B) {0} 0 α₁ P h α ζα ∧
    Lemma71G.IsLemma62Curve β (WholeField.centredField h u₀) P ∧
    Lemma71G.IsLemma62Curve γ₂ (WholeField.centredField h u₀) P ∧
    Lemma71G.IsLemma62Curve γ₁ (WholeField.centredField h u₀) P ∧
    Lemma71G.IsLemma62Curve α (WholeField.centredField h u₀) P ∧
    ∀ᵐ ω ∂P, ζβ ω = ⊤ ∧ ζ₂ ω = ⊤ ∧ ζ₁ ω = ⊤ ∧ ζα ω = ⊤ ∧
      IsSeedProper (β ω) ∧ IsSeedProper (γ₂ ω) ∧ IsSeedProper (γ₁ ω) ∧ IsSeedProper (α ω) ∧
      range (β ω) ⊆ closedLeftSide (γ₂ ω) ∧ range (β ω) ⊆ closedLeftSide (γ₁ ω) ∧
      range (β ω) ⊆ closedLeftSide (α ω) ∧ range (γ₂ ω) ⊆ closedLeftSide (γ₁ ω) ∧
      range (γ₂ ω) ⊆ closedLeftSide (α ω) ∧ range (γ₁ ω) ⊆ closedLeftSide (α ω)

/-- **One flow line of the configuration, with Lemma 6.2's hypotheses and complete simple proper paths** (the per-angle
step of `Lemma71H.exists_threeCurveSpace_nb`, with the same proof, plus `Prop55Half.IsFlowLine.ae_isSeedProper`). For
`0 < κ < 4`, a GFF with the data of Figure 7.1 whose values satisfy (4.4) for every angle of `[α₁, α₂]`, and an angle
`θ ∈ [α₁, α₂]`, there is a flow line of `h` with angle `θ` from `0` with Lemma 6.2's hypotheses for the centred field,
almost surely with infinite lifetime and a simple proper path from `0` off `ℝ ∖ {0}`. -/
theorem exists_flowLine_lemma62 (href : Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {α₁ α₂ θ A B : ℝ} (h1 : α₁ ≤ θ) (h2 : θ ≤ α₂)
    (hA : sleLambda κ - π * chiC κ + α₂ * chiC κ ≤ A) (hB : sleLambda κ - α₁ * chiC κ ≤ B)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (prop74Data A B) ((({0} : Finset ℝ)) : Set ℝ)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (prop74Data A B) ((({0} : Finset ℝ)) : Set ℝ) u₀) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ (prop74Data A B) {0} 0 θ P h η ζ ∧
      Lemma71G.IsLemma62Curve η (WholeField.centredField h u₀) P ∧
      ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsSeedProper (η ω) := by
  have hbpc := isPiecewiseConstant_prop74Data A B
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  have hB41 : sleLambda κ - π * chiC κ - α₁ * chiC κ ≤ B := by linarith
  have hF := Theorem15.isOrderedForceWord_flowLine (prop74Data A B) {0} 0
  have hθχ1 : α₁ * chiC κ ≤ θ * chiC κ := mul_le_mul_of_nonneg_right h1 hχ.le
  have hθχ2 : θ * chiC κ ≤ α₂ * chiC κ := mul_le_mul_of_nonneg_right h2 hχ.le
  have h44 := Lemma71H.cond44_flowLine_prop74Data (θ := θ) hκ (a := A) (b := B) (by linarith) (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL (prop74Data A B) {0} 0)
      (flowLineXR (prop74Data A B) {0} 0) (flowLineRhoL κ (prop74Data A B) {0} 0 θ)
      (flowLineRhoR κ (prop74Data A B) {0} 0 θ) := Lemma71H.hasFieldDeterminedHistories_of_cond44 href hκ hκ4 hF h44
  obtain ⟨η₀, ζ, hη₀⟩ := Lemma71H.exists_isFlowLine_of_det hκ hκ4.le hbpc hh hadm hdet
  obtain ⟨Φ, hΦm, hΦ⟩ := Lemma75Bridge.exists_flowLineMap_of_admissible hκ hκ4.le hadm
    (href κ hκ hκ4 _ _ _ _ hF h44)
  obtain ⟨hL, hR⟩ := Lemma71G.prop74Data_remark41 hκ hκ4 h1 h2 hA hB41
  obtain ⟨η, hη, hae⟩ := Lemma71H.exists_lemma62Version_of_map WholeField.retainedRangeEntranceStatement hκ hκ4 hbpc
    hh hL hR hη₀ ⟨Φ, hΦm, hΦ P h hh η₀ ζ hη₀⟩ hu₀
  have hfl : IsFlowLine κ (prop74Data A B) {0} 0 θ P h η ζ :=
    Lemma71G.IsFlowLine.congr_ae hη₀ (hae.mono fun ω hω => hω.2.1)
  refine ⟨η, ζ, hfl, hη, ?_⟩
  filter_upwards [IsFlowLine.ae_isSeedProper hκ hκ4.le hbpc hL hR hfl] with ω hω
  exact hω

/-- **The four-curve space exists** (§7.1 setup with two middle curves) from the §4.2 reference and Proposition 5.5
in `ℍ` (ruling R43: neither uses Lemma 7.1). For `0 < κ < 4`, angles `α₁ < θ₁ < θ₂ < α₂` and boundary values with
(5.2) for the outer pair (`B ≥ λ − α₁χ`, `A ≥ λ − πχ + α₂χ`), one probability space carries the configuration.
Conditional helper. -/
theorem exists_isFourCurveSpace (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {α₁ θ₁ θ₂ α₂ A B : ℝ}
    (h1 : α₁ < θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ < α₂)
    (hA : sleLambda κ - π * chiC κ + α₂ * chiC κ ≤ A) (hB : sleLambda κ - α₁ * chiC κ ≤ B) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β γ₂ γ₁ α : Ω → ℝ≥0 → ℂ) (ζβ ζ₂ ζ₁ ζα : Ω → ℝ≥0∞),
      IsFourCurveSpace κ α₁ θ₁ θ₂ α₂ A B P h u₀ β γ₂ γ₁ α ζβ ζ₂ ζ₁ ζα := by
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := Lemma71G.exists_isGFFWithBoundaryData_prop74Data.{u} hκ A B
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension (isPiecewiseConstant_prop74Data A B)
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  -- (5.2) for every pair of angles in `[α₁, α₂]`
  have hpair : ∀ θ θ', α₁ ≤ θ → θ' ≤ α₂ →
      sleLambda κ - θ * chiC κ ≤ B ∧ sleLambda κ - π * chiC κ + θ' * chiC κ ≤ A := fun θ θ' hθ hθ' =>
    ⟨by nlinarith [mul_le_mul_of_nonneg_right hθ hχ.le], by nlinarith [mul_le_mul_of_nonneg_right hθ' hχ.le]⟩
  obtain ⟨β, ζβ, hβf, hβ, hβa⟩ := exists_flowLine_lemma62 href hκ hκ4 (h1.trans (h12.trans h2)).le le_rfl hA hB hh hu₀
  obtain ⟨γ₂, ζ₂, h₂f, h₂, h₂a⟩ := exists_flowLine_lemma62 href hκ hκ4 (h1.trans h12).le h2.le hA hB hh hu₀
  obtain ⟨γ₁, ζ₁, h₁f, h₁, h₁a⟩ := exists_flowLine_lemma62 href hκ hκ4 h1.le (h12.trans h2).le hA hB hh hu₀
  obtain ⟨α, ζα, hαf, hα, hαa⟩ := exists_flowLine_lemma62 href hκ hκ4 le_rfl (h1.trans (h12.trans h2)).le hA hB hh hu₀
  -- the six orders (Proposition 5.5 in `ℍ`)
  have o₂β := h55 κ hκ hκ4 A B θ₂ α₂ h2 (hpair θ₂ α₂ (h1.trans h12).le le_rfl).1
    (hpair θ₂ α₂ (h1.trans h12).le le_rfl).2 P h hh γ₂ β ζ₂ ζβ h₂f hβf
  have o₁β := h55 κ hκ hκ4 A B θ₁ α₂ (h12.trans h2) (hpair θ₁ α₂ h1.le le_rfl).1
    (hpair θ₁ α₂ h1.le le_rfl).2 P h hh γ₁ β ζ₁ ζβ h₁f hβf
  have oαβ := h55 κ hκ hκ4 A B α₁ α₂ (h1.trans (h12.trans h2)) (hpair α₁ α₂ le_rfl le_rfl).1
    (hpair α₁ α₂ le_rfl le_rfl).2 P h hh α β ζα ζβ hαf hβf
  have o₁₂ := h55 κ hκ hκ4 A B θ₁ θ₂ h12 (hpair θ₁ θ₂ h1.le h2.le).1
    (hpair θ₁ θ₂ h1.le h2.le).2 P h hh γ₁ γ₂ ζ₁ ζ₂ h₁f h₂f
  have oα₂ := h55 κ hκ hκ4 A B α₁ θ₂ (h1.trans h12) (hpair α₁ θ₂ le_rfl h2.le).1
    (hpair α₁ θ₂ le_rfl h2.le).2 P h hh α γ₂ ζα ζ₂ hαf h₂f
  have oα₁ := h55 κ hκ hκ4 A B α₁ θ₁ h1 (hpair α₁ θ₁ le_rfl (h12.trans h2).le).1
    (hpair α₁ θ₁ le_rfl (h12.trans h2).le).2 P h hh α γ₁ ζα ζ₁ hαf h₁f
  refine ⟨Ω, mΩ, P, hP, h, u₀, β, γ₂, γ₁, α, ζβ, ζ₂, ζ₁, ζα, hh, hu₀,
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀, hβf, h₂f, h₁f, hαf, hβ, h₂, h₁, hα, ?_⟩
  filter_upwards [hβa, h₂a, h₁a, hαa, o₂β, o₁β, oαβ, o₁₂, oα₂, oα₁] with ω eβ e₂ e₁ eα r₂β r₁β rαβ r₁₂ rα₂ rα₁
  exact ⟨eβ.1, e₂.1, e₁.1, eα.1, eβ.2, e₂.2, e₁.2, eα.2, r₂β e₂.1 eβ.1, r₁β e₁.1 eβ.1, rαβ eα.1 eβ.1,
    r₁₂ e₁.1 e₂.1, rα₂ eα.1 e₂.1, rα₁ eα.1 e₁.1⟩

end InteractingSLE.Sec7.Lemma71Four
