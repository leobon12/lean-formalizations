/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37GermFlow
import InteractingSLE.Spec.Sec7.StripWallInputs
import InteractingSLE.Spec.Sec7.StripPocketPathWalls
import InteractingSLE.Spec.Sec5.GlueCond

/-!
# Aux. lemma 37's flow-side germ (G1) for the strip system: counterflow hull at a fixed time plus the two walls

Packet PROVE-STRIPSYS36, item (G1), for the strip system (specification §7.4.1, pp. 408–411; Aux. lemmas 36–37,
pp. 196–199). At a deterministic time `t` the exploration of Aux. lemma 37 is the filled counterflow hull
`m⁻¹(K′_t)` (`Sec5.GlueCond.cfHullQ t`, read from the counterflow's killed history) together with the complete walls
`α = η^{1,∞}_{−π/2,θ₁}` and `β^{(r)} = η^{r,∞}_{π/2,θ₂}`.

* `measurable_cfHull`, `isLocalSet_cfHull`: the counterflow hull at a fixed time is a hitting-measurable local set of
  the centred field `h − u₀` (the frozen counterflow coupling, `Sec5.GlueCond.isLocalSet_cfHullQ`).
* `ae_ownHeights_union_twoAngle`: `Aux37Germ.ae_ownHeights_union` for two two-angle walls with the (4.4) heights at
  their initial angles (the side heights at rational stops from `StripWall.ae_sideHeights_wall`).
* **`ae_ownHeights_union_strip`** (G1 for the strip system): almost surely, for every harmonic representative `v` of a
  version of the mean of `m⁻¹(K′_t) ∪ α ∪ β^{(r)}`, every flow chart of a change pocket of the walls (pocket on the
  left of `α`), every point `β^{(r)}(s)` (`s ≠ r`, off `α`) and `α(s)` (`s ≠ 1`, off `β^{(r)}`) at positive distance
  from the counterflow hull has an own time `q > s` at which the union mean has the wall's own height along the
  pocket approach: `λ − θ_L(s)χ` on `β^{(r)}` (`θ_L = π/2` before `r`, `θ₂` after), `−λ − θ_R(s)χ` on `α`
  (`θ_R = −π/2` before `1`, `θ₁` after), in the wall's own coordinate `f_q` of its concatenated driver.

The walls' determination comes from `h44` (the §4.2 reference, R48-safe), as in `StripWall.ae_eqOn_changePocket_strip`.
No Theorem 1.2/1.3 (R43, R48). Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Aux37Germ

open QuantumZipper (H Hbar logDerivFwd fwdMap chiC)
open PocketCoord PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux119Heights StripWall
  StripSideHeightProb
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-! ### The counterflow hull at a fixed time -/

/-- The strip system's counterflow hull at time `t`, in the flow chart: `m⁻¹(K′_t)` read from the killed history. -/
def cfHull (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  Sec5.GlueCond.cfHullQ t (Sec5.Cond44Ref.cfHistory W' ζ' ω)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurable_cfHull {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (t : ℝ≥0) :
    Measurable[mΩ, hittingSigma] (cfHull W' ζ' t) :=
  (Sec5.GlueCond.measurable_cfHullQ t).comp (Sec5.Cond44Ref.measurable_cfHistory
    (Sec5.Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf))

/-- **The strip system's counterflow hull at a fixed time is a local set of the centred field.** -/
theorem isLocalSet_cfHull {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    (u₀ : ℂ → ℝ) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (t : ℝ≥0) :
    IsLocalSet (cfHull W' ζ' t) (WholeField.centredField h u₀) P := by
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [StripPocketPath.ae_counterflow_trace hS hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  exact WholeField.IsLocalSet.sub_dist (Sec5.GlueCond.isLocalSet_cfHullQ hS.counterflow hreg t)
    (WholeField.isHarmonicDistOn_smoothDist hu₀)

/-! ### Two two-angle walls -/

section TwoAngle

/-- **(G1) for two two-angle walls and any local set `A`** (the walls as in `StripWall.ae_eqOn_changePocket_twoAngle`):
almost surely, for every harmonic representative `v` of the mean of `A ∪ walls`, every flow chart of a change pocket
on the left of `Rw`, the walls' own heights along the pocket approach at every wall point off the other wall and the
angle change, at positive distance from `A`. -/
theorem ae_ownHeights_union_twoAngle (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {θL₀ θL : ℝ} {tL : ℝ≥0} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hEL : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θL₀ tL θL) EL)
    (hregL : ∀ j ω, IsRegularDriver (EL j ω))
    (hLL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θL₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hLR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θL₀ * chiC κ)
    (hDL : IsDetTwoPiece P h EL) {Lw : Ω → ℝ≥0 → ℂ} (hvL : IsWallVersion P EL tL Lw)
    (hlocL : Sec6.IsEntranceHistoryLocal Lw (WholeField.centredField h u₀) P)
    {θR₀ θR : ℝ} {tR : ℝ≥0} {ER : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hER : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θR₀ tR θR) ER)
    (hregR : ∀ j ω, IsRegularDriver (ER j ω))
    (hRL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θR₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hRR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θR₀ * chiC κ)
    (hDR : IsDetTwoPiece P h ER) {Rw : Ω → ℝ≥0 → ℂ} (hvR : IsWallVersion P ER tR Rw)
    (hlocR : Sec6.IsEntranceHistoryLocal Rw (WholeField.centredField h u₀) P)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A (WholeField.centredField h u₀) P)
    {g gU : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ wallUnion Lw Rw ω) (WholeField.centredField h u₀) P g)
    (hgU : IsLocalSetMean (wallUnion Lw Rw) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Lw ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => Rw ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gR q)) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A ω ∪ wallUnion Lw Rw ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ wallUnion Lw Rw ω) → g ω φ = ∫ z, v z * φ z) →
      ∀ (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (Rw ω) (Lw ω) r Ψ c →
      changePocket (Rw ω) (Lw ω) r ⊆ leftSideOf (range (Rw ω)) →
      (∀ s : ℝ≥0, Lw ω s ∉ range (Rw ω) → s ≠ tL → (∃ ε > 0, A ω ∩ ball (Lw ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ *
            (logDerivFwd (fun t : ℝ => catPath (EL 0 ω).1 tL (EL 1 ω).1 t.toNNReal) q z).im)
          (𝓝[changePocket (Rw ω) (Lw ω) r] (Lw ω s))
          (𝓝 (sleLambda κ - (if s < tL then θL₀ else θL) * chiC κ))) ∧
      (∀ s : ℝ≥0, Rw ω s ∉ range (Lw ω) → s ≠ tR → (∃ ε > 0, A ω ∩ ball (Rw ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ *
            (logDerivFwd (fun t : ℝ => catPath (ER 0 ω).1 tR (ER 1 ω).1 t.toNNReal) q z).im)
          (𝓝[changePocket (Rw ω) (Lw ω) r] (Rw ω s))
          (𝓝 (-sleLambda κ - (if s < tR then θR₀ else θR) * chiC κ))) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hLdet := hDL.hdet hregL u₀ hvL.ae_isGeneratingTrace
  have hRdet := hDR.hdet hregR u₀ hvR.ae_isGeneratingTrace
  have htr : ∀ᵐ ω ∂P, Tendsto (Lw ω) atTop (cobounded ℂ) ∧ Tendsto (Rw ω) atTop (cobounded ℂ) := by
    filter_upwards [hvL.ae_trace, hvR.ae_trace] with ω hL hR
    exact ⟨hL.2.2.2, hR.2.2.2⟩
  have hsideL := ae_sideHeights_wall hκ hκ4 hb hh hEL hregL hLL0 hLR0 hDL.ae_lifetimes hu₀ hvL.continuous
    hvL.zero hvL.measurable hLdet hlocL hvL.ae_simple hgL hvR.zero
  have hsideR := ae_sideHeights_wall hκ hκ4 hb hh hER hregR hRL0 hRR0 hDR.ae_lifetimes hu₀ hvR.continuous
    hvR.zero hvR.measurable hRdet hlocR hvR.ae_simple hgR hvL.zero
  have key := ae_ownHeights_union hX hvL.continuous hvL.zero hvL.measurable hLdet hlocL hvL.ae_im_nonneg
    hvR.continuous hvR.zero hvR.measurable hRdet hlocR hvR.ae_im_nonneg htr hAm hAloc hg hgU hgL hgR
    (θL := fun s => if s < tL then θL₀ else θL) (θR := fun s => if s < tR then θR₀ else θR) hsideL hsideR
  filter_upwards [key, hvL.ae_trace, hvR.ae_trace, hDL.ae_lifetimes, hDR.ae_lifetimes]
    with ω hk hL hR hlL hlR v hv hrep r Ψ c hF hCl
  obtain ⟨hcL, hcL0⟩ := continuous_catPath_of_isRegularDriver (hregL 0 ω) (hregL 1 ω) hlL.1 hlL.2 tL
  obtain ⟨hcR, hcR0⟩ := continuous_catPath_of_isRegularDriver (hregR 0 ω) (hregR 1 ω) hlR.1 hlR.2 tR
  obtain ⟨k1, k2⟩ := hk v hv hrep r Ψ c hF hCl hL.1 hcL hcL0 hR.1 hcR hcR0
  exact ⟨fun s hs hst hA => k1 s hs (by simpa using hst) hA, fun s hs hst hA => k2 s hs (by simpa using hst) hA⟩

end TwoAngle

/-! ### The strip system -/

section Strip

/-- **(G1) for the strip system** (see the module docstring): the walls `β = β^{(r)}`, `α` of the strip system with
Aux. lemma 130's heights, versions of their traces, their entrance-history locality, any hitting-measurable local set
`A` (e.g. the counterflow hull at a fixed time, `isLocalSet_cfHull`), and versions of the means. -/
theorem ae_ownHeights_union_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A (WholeField.centredField h u₀) P)
    {g gU : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ wallUnion β α ω) (WholeField.centredField h u₀) P g)
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => β ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gR q)) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A ω ∪ wallUnion β α ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ wallUnion β α ω) → g ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (α ω) (β ω) r' Ψ c →
      changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      (∀ s : ℝ≥0, β ω s ∉ range (α ω) → s ≠ r → (∃ ε > 0, A ω ∩ ball (β ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ =>
            catPath (E (StripSys.betaSpec r θ₂) 0 ω).1 r (E (StripSys.betaSpec r θ₂) 1 ω).1 t.toNNReal) q z).im)
          (𝓝[changePocket (α ω) (β ω) r'] (β ω s))
          (𝓝 (sleLambda κ - (if s < r then π / 2 else θ₂) * chiC κ))) ∧
      (∀ s : ℝ≥0, α ω s ∉ range (β ω) → s ≠ 1 → (∃ ε > 0, A ω ∩ ball (α ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ =>
            catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1 (E (StripSys.alphaSpec θ₁) 1 ω).1 t.toNNReal) q z).im)
          (𝓝[changePocket (α ω) (β ω) r'] (α ω s))
          (𝓝 (-sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ))) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEα : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec (-(π / 2)) 1 θ₁) (E (StripSys.alphaSpec θ₁)) :=
    hS.isStagedHistory_alpha hθ₁
  have hEβ : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec (π / 2) r θ₂) (E (StripSys.betaSpec r θ₂)) :=
    hS.isStagedHistory_beta hθ₂ r
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh hEα hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) (hcumR _ hθ₁)
      hθ₁.1 (by linarith [hθ₁.2])
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec r θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hEβ hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂)
      (fun y hy hyJ => by have := hcumR _ hθ₂ y hy hyJ; linarith) hθ₂.2 (by linarith [hθ₂.1])
  exact ae_ownHeights_union_twoAngle hκ hκ4 hb hh hu₀ hEβ hregβ (hL44 _ hp) (hcumR _ hp) hDβ hvβ hlocβ
    hEα hregα (hL44 _ hm) (hcumR _ hm) hDα hvα hlocα hAm hAloc hg hgU hgL hgR

end Strip

end InteractingSLE.Sec7.Aux37Germ
