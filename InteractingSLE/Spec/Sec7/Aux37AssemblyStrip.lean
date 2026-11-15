/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37AssemblyWitness

/-!
# Aux. lemma 37 for the strip system: no witness frame, almost surely

Packet PROVE-STRIPSYS39, item (3), field part. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md`
L104–L136, pp. 198–200).

For the strip system, the walls `β = β^{(r)}` (left, stage time `r`) and `α` (right), the exploration
`E_t = stripExpl W′ ζ′ β α t = m(K′_t) ∪ walls` with versions `g t` of its means, and two deterministic times
`r₀ ≤ s₀`:

* **`ae_noFrame_strip`**: almost surely, for every flow chart of the change pocket on the left of `α`, neither witness
  frame (`IsRightWitnessFrame`, `IsLeftWitnessFrame`) exists. Inputs: the flat clock `FlatClockStatement` for the
  exploration (FC, the named input), and the hypotheses of the proved germs — (G1) `Aux37Germ.ae_ownHeights_union_strip`
  at `r₀` (the counterflow hull at `r₀` as the local set), (G2) `ae_cfGerm_union_strip` at `s₀`.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48); `h44` is the walls'
determination input, as in G1.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Aux37Assembly

open QuantumZipper (H Hbar chiC fwdHull fwdMap logDerivFwd)
open WangWu (negInv)
open PocketCoord PocketJordan PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux37Germ StripWall
  StripSideHeightProb
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- The own driver of the right wall `α = η^{1,∞}_{−π/2,θ₁}` (the concatenated two-angle driver, real time). -/
def alphaDrv (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (θ₁ : ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1 (E (StripSys.alphaSpec θ₁) 1 ω).1 t.toNNReal

/-- The own driver of the left wall `β^{(r)} = η^{r,∞}_{π/2,θ₂}` (the concatenated two-angle driver, real time). -/
def betaDrv (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (r : ℝ≥0) (θ₂ : ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => catPath (E (StripSys.betaSpec r θ₂) 0 ω).1 r (E (StripSys.betaSpec r θ₂) 1 ω).1 t.toNNReal

/-- **No witness frame, almost surely** (Aux. lemma 37's field comparison for the strip system at the deterministic
times `r₀ ≤ s₀`; see the module docstring). -/
theorem ae_noFrame_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => β ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL t))
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ t : ℝ≥0, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t))
    (hFC : FlatClockStatement P univ (stripExpl W' ζ' β α) g) {r₀ s₀ : ℝ≥0} (hrs : r₀ ≤ s₀) :
    ∀ᵐ ω ∂P, ∀ (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (α ω) (β ω) r Ψ c →
      changePocket (α ω) (β ω) r ⊆ leftSideOf (range (α ω)) →
      ¬ IsRightWitnessFrame (α ω) (β ω) r (cfHull W' ζ' r₀ ω) (cfHull W' ζ' s₀ ω) (wallUnion β α ω)
          (stripExpl W' ζ' β α r₀ ω) (stripExpl W' ζ' β α s₀ ω) (fun t : ℝ => W' t.toNNReal ω)
          (alphaDrv E θ₁ ω) s₀ (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) s₀)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) s₀) ∧
        ¬ IsLeftWitnessFrame (α ω) (β ω) r (cfHull W' ζ' r₀ ω) (cfHull W' ζ' s₀ ω) (wallUnion β α ω)
          (stripExpl W' ζ' β α r₀ ω) (stripExpl W' ζ' β α s₀ ω) (fun t : ℝ => W' t.toNNReal ω)
          (betaDrv E r θ₂ ω) s₀ (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) s₀)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) s₀) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
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
  have hLdet := hDβ.hdet hregβ u₀ hvβ.ae_isGeneratingTrace
  have hRdet := hDα.hdet hregα u₀ hvα.ae_isGeneratingTrace
  have htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ) := by
    filter_upwards [hvβ.ae_trace, hvα.ae_trace] with ω hL hR
    exact ⟨hL.2.2.2, hR.2.2.2⟩
  have G1 := ae_ownHeights_union_strip h44 hS hcumL hcumR hθ₁c hθ₂c r hregα hregβ hu₀ hvβ hlocβ hvα hlocα
    (measurable_cfHull hS.counterflow r₀) (isLocalSet_cfHull hS hcumL hcumR u₀ hu₀.1 r₀) (hg r₀) hgU hgL hgR
  have G2 := ae_cfGerm_union_strip hS hcumL hcumR hu₀ hvβ.continuous hvβ.zero hvβ.measurable hLdet hlocβ
    hvα.continuous hvα.zero hvα.measurable hRdet hlocα htr s₀ (hg s₀)
  have FC := hFC r₀ trivial s₀ trivial hrs
  filter_upwards [G1, G2, FC, (hg r₀).2.1, (hg s₀).2.1] with ω h1 h2 h3 ⟨vr, hvr, hvrr⟩ ⟨vs, hvs, hvsr⟩ Ψ c hF hCl
  obtain ⟨g1L, g1R⟩ := h1 vr hvr hvrr r Ψ c hF hCl
  have g2 := h2 vs hvs hvsr
  have fc := fun z hz hcomp => h3 vr vs hvr hvrr hvs hvsr z hz hcomp
  refine ⟨fun hfr => ?_, fun hfr => ?_⟩
  · exact false_of_rightFrame (u₀ := u₀) hκ hκ4 hθ₁ g1R
      (fun z₀ hz₀ hε F hF y hy hyJ hy0 hyR => (g2 z₀ hz₀ hε F hF y hy hyJ).2 hy0 hyR) fc hfr
  · exact false_of_leftFrame (u₀ := u₀) hκ hκ4 hθ₂ g1L
      (fun z₀ hz₀ hε F hF y hy hyJ hy0 hyL => (g2 z₀ hz₀ hε F hF y hy hyJ).1 hy0 hyL) fc hfr

/-! ### `hwit` and `hwitI` from the witness frames -/

open StripPocketPath in
/-- **The witness frame statement** (Aux. lemma 37's geometric bridges, a named pathwise input): almost surely, every
rational witness of attachment progress in the change pocket of `α` and `β^{(q)} = Lr q` (either pocket shape) comes
with a flow chart of the pocket, the pocket on the left of `α`, and a witness frame on `α` or on `β^{(q)}` at the
deterministic times `r₀ = s₁⁺`, `s₀ = s₂⁺` (see `IsRightWitnessFrame`). -/
def WitnessFrameStatement (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (P : Measure Ω) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (θ₁ θ₂ : ℝ) (α : Ω → ℝ≥0 → ℂ)
    (Lr : ℚ → Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ) : Prop :=
  ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
    (IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ ∨
      IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂) →
    (∃ (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (α ω) (Lr q ω) (StripSys.rt q) Ψ c) ∧
      changePocket (α ω) (Lr q ω) (StripSys.rt q) ⊆ leftSideOf (range (α ω)) ∧
      (IsRightWitnessFrame (α ω) (Lr q ω) (StripSys.rt q) (cfHull W' ζ' (s₁ : ℝ).toNNReal ω)
          (cfHull W' ζ' (s₂ : ℝ).toNNReal ω) (wallUnion (Lr q) α ω) (stripExpl W' ζ' (Lr q) α (s₁ : ℝ).toNNReal ω)
          (stripExpl W' ζ' (Lr q) α (s₂ : ℝ).toNNReal ω) (fun t : ℝ => W' t.toNNReal ω) (alphaDrv E θ₁ ω)
          (s₂ : ℝ).toNNReal (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) (s₂ : ℝ).toNNReal)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) (s₂ : ℝ).toNNReal) ∨
        IsLeftWitnessFrame (α ω) (Lr q ω) (StripSys.rt q) (cfHull W' ζ' (s₁ : ℝ).toNNReal ω)
          (cfHull W' ζ' (s₂ : ℝ).toNNReal ω) (wallUnion (Lr q) α ω) (stripExpl W' ζ' (Lr q) α (s₁ : ℝ).toNNReal ω)
          (stripExpl W' ζ' (Lr q) α (s₂ : ℝ).toNNReal ω) (fun t : ℝ => W' t.toNNReal ω)
          (betaDrv E (StripSys.rt q) θ₂ ω) (s₂ : ℝ).toNNReal
          (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) (s₂ : ℝ).toNNReal)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) (s₂ : ℝ).toNNReal))

open StripPocketPath in
/-- **`hwit` and `hwitI` of `StripPocketPath.pocketWordEvolution_of_stripSystem`** (Aux. lemma 37's exclusion of every
rational witness), exactly in their types, from the flat clock (FC) for each pocket's exploration and the witness frame
statement, with the hypotheses of the proved germs (G1: the walls' versions, locality and means; G2: none beyond the
strip system). Angles: `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]` (for `θ₂ = −π/2` the phase does not exclude the left
wall's second piece, PROVE-STRIPSYS34). -/
theorem hwit_hwitI_of_frame (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
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
    {g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t))
    (hFC : ∀ q : ℚ, 0 < q → FlatClockStatement P univ (stripExpl W' ζ' (Lr q) α) (g q))
    (hframe : WitnessFrameStatement κ b jumps P W' ζ' E θ₁ θ₂ α Lr η) :
    (∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂) ∧
    (∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂) := by
  have key : ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, (s₁ : ℝ) < s₂ → ∀ᵐ ω ∂P,
      IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      ¬ (IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ ∨
        IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂) := by
    intro q hq s₁ s₂ v v₁ v₂ hlt
    have hrs : (s₁ : ℝ).toNNReal ≤ (s₂ : ℝ).toNNReal := Real.toNNReal_le_toNNReal hlt.le
    filter_upwards [ae_noFrame_strip h44 hS hcumL hcumR hθ₁ hθ₂ (StripSys.rt q) hregα (hregβ q hq) hu₀ (hvL q hq)
      (hlocL q hq) hvα hlocα (hgU q hq) (hgL q hq) hgR (hg q hq) (hFC q hq) hrs,
      hframe q hq s₁ s₂ v v₁ v₂] with ω hno hfr hconf hw
    obtain ⟨⟨Ψ, c, hF⟩, hCl, hfr'⟩ := hfr hconf hw
    rcases hfr' with hR | hL
    · exact (hno Ψ c hF hCl).1 hR
    · exact (hno Ψ c hF hCl).2 hL
  refine ⟨fun q hq s₁ s₂ v v₁ v₂ => ?_, fun q hq s₁ s₂ v v₁ v₂ => ?_⟩
  · by_cases hlt : (s₁ : ℝ) < s₂
    · filter_upwards [key q hq s₁ s₂ v v₁ v₂ hlt] with ω hk hconf _ hw using hk hconf (Or.inl hw)
    · refine Eventually.of_forall fun ω _ _ hw => hlt ?_
      rcases hw.1 with h1 | h1
      · exact h1.2.1
      · exact h1.2.1
  · by_cases hlt : (s₁ : ℝ) < s₂
    · filter_upwards [key q hq s₁ s₂ v v₁ v₂ hlt] with ω hk hconf _ hw using hk hconf (Or.inr hw)
    · refine Eventually.of_forall fun ω _ _ hw => hlt ?_
      rcases hw.1 with h1 | h1
      · exact h1.2.1
      · exact h1.2.1

end InteractingSLE.Sec7.Aux37Assembly
