/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofWire
import InteractingSLE.Spec.Sec7.Aux37SideAssembly
import InteractingSLE.Spec.Sec7.Aux37SideInfFrame

/-!
# Aux. lemma 37's witness exclusions with the flat clock discharged

Packet PROVE-FLATCLOCK. PROVE-STRIPSYS42's `Aux37Side.hwit_of_flatClock` and `Aux37Side.hwitI_of_flatClock` take the
flat clock (FC) as their only named field input `hFC`, for versions `g` of the means of the strip exploration. Both are
now proved (`flatClockStatement_strip_rat`, `exists_isLocalSetMean_strip_rat`), so:

* **`hwit_of_wallMeans`**: `hwit` of `StripPocketPath.pocketWordEvolution_of_stripSystem` (the bounded change pocket),
  from the binders of `hwit_of_flatClock` without `g`, `hg`, `hFC`;
* **`hwitI_of_wallMeans`**: `hwitI` (the change pocket at the flow seed), from the binders of `hwitI_of_flatClock`
  without `g`, `hg`, `hFC`.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48); `h44` is the walls'
determination input, as in the consumers.
-/

set_option autoImplicit false

noncomputable section

universe u

open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.FlatClockProof

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **`hwit` without the flat clock and the exploration means**: `Aux37Side.hwit_of_flatClock` with the versions `g`
of the means of the strip exploration supplied by `exists_isLocalSetMean_strip_rat` and `hFC` discharged by
`flatClockStatement_strip_rat`; the remaining field inputs are the walls' means `gU`, `gL`, `gR`. Angles
`θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`. -/
theorem hwit_of_wallMeans (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨g, hg⟩ := exists_isLocalSetMean_strip_rat h44 hS hcumL hcumR (Ioo_subset_Icc_self hθ₁)
    (Ioc_subset_Icc_self hθ₂) hregα hregβ hu₀ hvα hlocα hvL hlocL
  exact Aux37Side.hwit_of_flatClock h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀ hvα hlocα hvL hlocL hgU hgL hgR hg
    (flatClockStatement_strip_rat h44 hS hcumL hcumR (Ioo_subset_Icc_self hθ₁) (Ioc_subset_Icc_self hθ₂) hregα
      hregβ hu₀ hvα hlocα hvL hlocL hg) hηc hηtr hwalls hwallsL hβ hLβ hav

/-- **`hwitI` without the flat clock and the exploration means**: `Aux37Side.hwitI_of_flatClock` with `g` from
`exists_isLocalSetMean_strip_rat` and `hFC` from `flatClockStatement_strip_rat`. Angles `θ₁ ∈ (−π/2, π/2)`,
`θ₂ ∈ (−π/2, π/2]`. -/
theorem hwitI_of_wallMeans (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨g, hg⟩ := exists_isLocalSetMean_strip_rat h44 hS hcumL hcumR (Ioo_subset_Icc_self hθ₁)
    (Ioc_subset_Icc_self hθ₂) hregα hregβ hu₀ hvα hlocα hvL hlocL
  exact Aux37Side.hwitI_of_flatClock h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀ hvα hlocα hvL hlocL hgU hgL hgR hg
    (flatClockStatement_strip_rat h44 hS hcumL hcumR (Ioo_subset_Icc_self hθ₁) (Ioc_subset_Icc_self hθ₂) hregα
      hregβ hu₀ hvα hlocα hvL hlocL hg) hηc hηtr hwalls hwallsL hβ hLβ hav

end InteractingSLE.Sec7.FlatClockProof
