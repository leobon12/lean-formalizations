/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC14Marked
import InteractingSLE.Spec.Sec7.SideC14Strip

/-!
# The original filled-pocket flow formula for the installed two-angle strip

PROVE-SIDE-COLLAR2. The actual strip system supplies wall determination,
entrance locality, all marked laws, regularization, and the wall-union
mean. Only the geometric selection of the pocket and the chosen version
of its exterior mean are inputs to the general filled-pocket statement.
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
open PocketCoord PocketMarks StripGeom Lemma71N

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
  [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- The actual two-angle strip-data instantiation of the original filled
mean formula, for an arbitrary selected change pocket and every mean version. -/
theorem ae_eqOn_filledPocket_twoAngleStrip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : WordSafe.IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ} (hq : 0 < q)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) β)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    {C : Ω → Set ℂ} {gC : Ω → DistOn upperHalfPlaneOpens}
    (hCm : Measurable[PocketWordPerQ.wallsSigma P α β, hittingSigma] (fun ω => H \ C ω))
    (hCo : ∀ ω, IsOpen (C ω)) (hCs : ∀ ω, C ω ⊆ H \ wallUnion β α ω)
    (hCc : ∀ᵐ ω ∂P, ∀ z ∈ C ω, connectedComponentIn (H \ wallUnion β α ω) z ⊆ C ω)
    (hgC : IsLocalSetMean (fun ω => H \ C ω) (WholeField.centredField h u₀) P gC) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (C ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω → gC ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      C ω = changePocket (α ω) (β ω) r' →
      IsFlowChart (α ω) (β ω) r' Ψ c → changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r') →
      (∀ z ∈ changePocket (α ω) (β ω) r', c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < StripSys.rt q then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {StripSys.rt q} {1} c) G →
      ∀ z ∈ C ω, v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hS' := WordSafe.isTwoAngle_regTwo hS hcumL hcumR
  have hvβ' := WordSafe.isWallVersion_regTwo hS hcumL hcumR
    StripSys.pi_div_two_mem_Icc hθ₂ hvβ
  have hvα' := WordSafe.isWallVersion_regTwo hS hcumL hcumR
    StripSys.neg_pi_div_two_mem_Icc hθ₁ hvα
  obtain ⟨hdα, hlα, hdβ, hlβ⟩ := WordSafe.wall_inputs h44 hS' hcumL hcumR hθ₁ hθ₂ hq
    (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _) (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _)
    hu₀ hvα' hvβ'
  have htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (Bornology.cobounded ℂ) ∧
      Tendsto (α ω) atTop (Bornology.cobounded ℂ) := by
    filter_upwards [hvβ.ae_trace, hvα.ae_trace] with ω hβ hα
    exact ⟨hβ.2.2.2, hα.2.2.2⟩
  obtain ⟨hUm, hUloc, -⟩ := isLocalSet_wallUnion hX hvβ.continuous hvβ.zero hvβ.measurable hdβ hlβ
    hvα.continuous hvα.zero hvα.measurable hdα hlα htr
  obtain ⟨gU, hgU⟩ := IsLocalSet.exists_isLocalSetMean hX hUm hUloc
  have hEq := ae_representatives_filled_eq_wallMean hX
    hvβ.continuous hvβ.zero hvβ.measurable hdβ hlβ
    hvα.continuous hvα.zero hvα.measurable hdα hlα htr hCm hCo hCs hCc hgU hgC
  have hSource := ae_eqOn_changePocket_twoAngleStrip_reg h44 hS hcumL hcumR hθ₁ hθ₂ hq
    hu₀ hvβ hvα hgU
  filter_upwards [hEq, hSource, hgU.2.1] with ω hEqω hSourceω hgUω
    v hv hrep r' Ψ c ℓ n G hC hc hleft hℓ hlift hn hG z hz
  obtain ⟨hu, hrepU⟩ := Aux119Heights.harmRep_spec hgUω
  have heq := hEqω v (Aux119Heights.harmRep (gU ω) (H \ wallUnion β α ω)) hv hrep hu hrepU hz
  rw [heq]
  exact hSourceω _ hu hrepU r' Ψ c ℓ n G hc hleft hℓ hlift hn hG z (hC ▸ hz)

end InteractingSLE.Sec7.SideC14
