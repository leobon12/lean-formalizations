/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofStrip
import InteractingSLE.Spec.Sec7.StripWallInputsReflDet

/-!
# Aux. lemma 37's flat clock for the strip system's walls

Packet PROVE-FLATCLOCK. The flat clock `Aux37Germ.FlatClockStatement` (Aux. lemma 37, p. 198) for the strip exploration
`stripExpl W′ ζ′ β α`, with the walls' Lemma 6.2 inputs supplied as in PROVE-STRIPSYS39's
`Aux37Assembly.ae_noFrame_strip`:
field determination from `h44` (`StripWall.isDetTwoPiece_of_heights`, `…_refl`), continuity, start, measurability and
transience from the wall versions (`IsWallVersion`).

* `strip_walls_inputs`: the walls' field determination and transience;
* **`flatClockStatement_strip`**: one left wall `β = β^{(r)}` (angle `θ₂`, stage time `r`) and the right wall `α`
  (angle `θ₁`);
* **`flatClockStatement_strip_rat`**: the family `β^{(q)} = Lr q`, `q ∈ ℚ>0`, exactly the input `hFC` of
  `Aux37Side.hwit_of_flatClock` and `Aux37SideInf.hwitI_of_flatClock`;
* `exists_isLocalSetMean_strip`, **`exists_isLocalSetMean_strip_rat`**: the strip exploration is a local set and
  versions of its means exist (the input `hg` of the same consumers).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48); `h44` is the walls'
determination input (PROVE-FLATCLOCK packet: "`h44` may be kept").
-/

set_option autoImplicit false

noncomputable section

universe u

open MeasureTheory Filter Set Topology Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.FlatClockProof

open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open LocalSets Aux119Nested Aux37Germ StripWall
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The walls' Lemma 6.2 inputs for the strip system** (as in `Aux37Assembly.ae_noFrame_strip`): the left wall
`β = β^{(r)}` (angle `θ₂`) and the right wall `α` (angle `θ₁`) are determined by the centred field at every time
(from `h44`), and both are transient. -/
theorem strip_walls_inputs (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω)) (u₀ : ℂ → ℝ)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α) :
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    (∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ)) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEα := hS.isStagedHistory_alpha hθ₁c
  have hEβ := hS.isStagedHistory_beta hθ₂c r
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh hEα hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁c) (hcumR _ hθ₁c)
      hθ₁c.1 (by linarith [hθ₁c.2])
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec r θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hEβ hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂c)
      (fun y hy hyJ => by have := hcumR _ hθ₂c y hy hyJ; linarith) hθ₂c.2 (by linarith [hθ₂c.1])
  refine ⟨hDβ.hdet hregβ u₀ hvβ.ae_isGeneratingTrace, hDα.hdet hregα u₀ hvα.ae_isGeneratingTrace, ?_⟩
  filter_upwards [hvβ.ae_trace, hvα.ae_trace] with ω hL hR
  exact ⟨hL.2.2.2, hR.2.2.2⟩

/-- **The flat clock for the strip system's walls** `β = β^{(r)}` (left, angle `θ₂`) and `α` (right, angle `θ₁`):
`FlatClockStatement P univ (stripExpl W′ ζ′ β α) g` for every family `g` of versions of the means. -/
theorem flatClockStatement_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ t : ℝ≥0, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t)) :
    FlatClockStatement P univ (stripExpl W' ζ' β α) g := by
  obtain ⟨hβdet, hαdet, htr⟩ := strip_walls_inputs h44 hS hcumL hcumR hθ₁c hθ₂c r hregα hregβ u₀ hvβ hvα
  exact flatClockStatement_stripExpl_of_walls hS hcumL hcumR hu₀ hvβ.continuous hvβ.zero hvβ.measurable hβdet hlocβ
    hvα.continuous hvα.zero hvα.measurable hαdet hlocα htr hg

/-- **Versions of the means of the strip exploration exist** (and it is a local set at every time), for the strip
system's walls `β = β^{(r)}` and `α`. -/
theorem exists_isLocalSetMean_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P) :
    (∀ t, IsLocalSet (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P) ∧
      ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
        ∀ t, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t) := by
  obtain ⟨hβdet, hαdet, htr⟩ := strip_walls_inputs h44 hS hcumL hcumR hθ₁c hθ₂c r hregα hregβ u₀ hvβ hvα
  exact exists_isLocalSetMean_stripExpl_of_walls hS hcumL hcumR hu₀ hvβ.continuous hvβ.zero hvβ.measurable hβdet
    hlocβ hvα.continuous hvα.zero hvα.measurable hαdet hlocα htr

/-- **The flat clock for the family `β^{(q)} = Lr q`** (`q ∈ ℚ>0`, stage time `rt q`), exactly the input `hFC` of
`Aux37Side.hwit_of_flatClock` and `Aux37SideInf.hwitI_of_flatClock`. -/
theorem flatClockStatement_strip_rat (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t)) :
    ∀ q : ℚ, 0 < q → FlatClockStatement P univ (stripExpl W' ζ' (Lr q) α) (g q) := fun q hq =>
  flatClockStatement_strip h44 hS hcumL hcumR hθ₁c hθ₂c (StripSys.rt q) hregα (hregβ q hq) hu₀ (hvL q hq)
    (hlocL q hq) hvα hlocα (hg q hq)

/-- **Versions of the means for the family `β^{(q)} = Lr q`** (`q ∈ ℚ>0`): a family `g` as in the input `hg` of
`Aux37Side.hwit_of_flatClock` and `Aux37SideInf.hwitI_of_flatClock`. -/
theorem exists_isLocalSetMean_strip_rat (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P) :
    ∃ g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t) := by
  have hex : ∀ q : ℚ, ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g t) := fun q => by
    by_cases hq : 0 < q
    · obtain ⟨-, g, hg⟩ := exists_isLocalSetMean_strip h44 hS hcumL hcumR hθ₁c hθ₂c (StripSys.rt q) hregα
        (hregβ q hq) hu₀ (hvL q hq) (hlocL q hq) hvα hlocα
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hq⟩
  choose g hg using hex
  exact ⟨g, fun q hq t => hg q hq t⟩

end InteractingSLE.Sec7.FlatClockProof
