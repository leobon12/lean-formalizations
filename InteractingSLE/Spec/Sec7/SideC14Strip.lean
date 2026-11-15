/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.WordSafeReg
import InteractingSLE.Spec.Sec5.WordSafePort2

/-!
# The actual two-angle strip system's change-pocket flow formula

PROVE-SIDE-COLLAR2. Port only the two histories used by Aux. 119. No
full strip-system premise or Theorem 1.2/1.3 is needed. These statements
are for general change pockets and arbitrary versions of their means.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.SideC14

open LocalSets StripWall StripSideHeightProb Aux119Nested Aux119Bdry Aux2728Pocket
open PocketCoord PocketMarks StripGeom Lemma71N Exist.Staged

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
  [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- Aux. 119 with the two-angle strip system actually installed by the
word context. The proof uses the two staged histories separately. -/
theorem ae_eqOn_changePocket_twoAngleStrip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : WordSafe.IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
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
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => β ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gR q)) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion β α ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion β α ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (α ω) (β ω) r' Ψ c → changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r') →
      (∀ z ∈ changePocket (α ω) (β ω) r', c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < r then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {r} {1} c) G →
      ∀ z ∈ changePocket (α ω) (β ω) r', v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
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
  exact ae_eqOn_changePocket_twoAngle hκ hκ4 hb hh hu₀ hEβ hregβ (hL44 _ hp) (hcumR _ hp) hDβ hvβ hlocβ
    hEα hregα (hL44 _ hm) (hcumR _ hm) hDα hvα hlocα hgU hgL hgR


/-- General change pockets of the actual two-angle strip system, with
wall locality and every prefix mean proved from its own wall versions. -/
theorem ae_eqOn_changePocket_twoAngleStrip_loc (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : WordSafe.IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ} (hq : 0 < q)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) β)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion β α ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion β α ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (α ω) (β ω) r' Ψ c → changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r') →
      (∀ z ∈ changePocket (α ω) (β ω) r', c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < (StripSys.rt q) then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {StripSys.rt q} {1} c) G →
      ∀ z ∈ changePocket (α ω) (β ω) r', v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  obtain ⟨hdβ, hlβ, hdα, hlα, -⟩ := WordSafe.lemma62_walls_rat h44 hS hcumL hcumR
    hθ₁ hθ₂ hq hregα hregβ hu₀ hvβ.continuous hvβ.zero hvβ.measurable hvβ.ae_isGeneratingTrace
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace
  obtain ⟨gL, hgL⟩ := StripWall.exists_isLocalSetMean_prefix hX
    hvβ.continuous hvβ.zero hvβ.measurable hdβ hlβ
  obtain ⟨gR, hgR⟩ := StripWall.exists_isLocalSetMean_prefix hX
    hvα.continuous hvα.zero hvα.measurable hdα hlα
  exact ae_eqOn_changePocket_twoAngleStrip h44 hS hcumL hcumR hθ₁ hθ₂ (StripSys.rt q)
    hregα hregβ hu₀ hvβ hlβ hvα hlα hgU hgL hgR

/-- The installed strip histories need no additional regularity premise:
regularize their two programs and transfer the actual wall versions. -/
theorem ae_eqOn_changePocket_twoAngleStrip_reg (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : WordSafe.IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ} (hq : 0 < q)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) β)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion β α ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion β α ω → gU ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (α ω) (β ω) r' Ψ c → changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r') →
      (∀ z ∈ changePocket (α ω) (β ω) r', c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < (StripSys.rt q) then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {StripSys.rt q} {1} c) G →
      ∀ z ∈ changePocket (α ω) (β ω) r', v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  have hS' := WordSafe.isTwoAngle_regTwo hS hcumL hcumR
  have hvβ' := WordSafe.isWallVersion_regTwo hS hcumL hcumR
    StripSys.pi_div_two_mem_Icc hθ₂ hvβ
  have hvα' := WordSafe.isWallVersion_regTwo hS hcumL hcumR
    StripSys.neg_pi_div_two_mem_Icc hθ₁ hvα
  exact ae_eqOn_changePocket_twoAngleStrip_loc h44 hS' hcumL hcumR hθ₁ hθ₂ hq
    (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _) (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _)
    hu₀ hvβ' hvα' hgU

end InteractingSLE.Sec7.SideC14
