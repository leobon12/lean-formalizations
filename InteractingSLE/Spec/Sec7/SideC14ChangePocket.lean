/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC14FilledStrip
import InteractingSLE.Spec.Sec7.SideC14Select

/-!
# The original exterior mean of a general selected change pocket

PROVE-SIDE-COLLAR2. All component, selection, marking, wall-mean and
regularization premises are now proved from the actual two-angle strip
and its wall versions. The statement applies to the general pockets
used by both installed side tests and R.7's initial-height input.
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

/-- The original pocket-exterior flow formula from the actual strip data,
for every version and every harmonic representative of its mean. -/
theorem ae_eqOn_selectedChangePocket_twoAngleStrip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : WordSafe.IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ} (hq : 0 < q)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) β)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    {A : Set Ω} {r : ℝ≥0}
    (hA : MeasurableSet[PocketWordPerQ.wallsSigma P α β] A)
    (hcfg : ∀ ω ∈ A, IsChangeConfigInc (α ω) (β ω) r)
    {gC : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (fun ω => H \ selectedChangePocket A α β r ω)
      (WholeField.centredField h u₀) P gC) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (changePocket (α ω) (β ω) r) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ changePocket (α ω) (β ω) r →
        gC ω φ = ∫ z, v z * φ z) →
      ∀ (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (G : ℂ → ℝ),
      IsFlowChart (α ω) (β ω) r Ψ c → changePocket (α ω) (β ω) r ⊆ leftSideOf (range (α ω)) →
      IsDerivLog c.1 ℓ (changePocket (α ω) (β ω) r) →
      (∀ z ∈ changePocket (α ω) (β ω) r, c.2.2 z = (ℓ z).im) → IsPocketBranch (β ω) (α ω) c n →
      IsBoundedHarmonicExtension
        (chartData (β ω) (α ω) (fun s => sleLambda κ - (if s < StripSys.rt q then π / 2 else θ₂) * chiC κ)
          (fun s => -sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ) c)
        (exSet (β ω) (α ω) {StripSys.rt q} {1} c) G →
      ∀ z ∈ changePocket (α ω) (β ω) r,
        v z + u₀ z = G (c.1 z) - chiC κ * (c.2.2 z + 2 * π * n) := by
  have hRm := PocketWordPerQ.measurable_right_wallsSigma (P := P) hvα.continuous hvβ.continuous
  have hLm := PocketWordPerQ.measurable_left_wallsSigma (P := P) hvα.continuous hvβ.continuous
  have hCm := measurable_selectedChangePocket_exterior
    hvα.continuous hvβ.continuous hRm hLm hA hcfg
  obtain ⟨hCo, hCs, hCc⟩ := selectedChangePocket_geometry hcfg
  have hSource := ae_eqOn_filledPocket_twoAngleStrip h44 hS hcumL hcumR hθ₁ hθ₂ hq hu₀ hvβ hvα
    hCm hCo hCs (ae_of_all _ hCc) hgC
  filter_upwards [hSource] with ω hSourceω hω v hv hrep Ψ c ℓ n G hc hleft hℓ hlift hn hG
  simp only [selectedChangePocket, ite_eq_left hω] at hSourceω
  exact hSourceω v hv hrep r Ψ c ℓ n G rfl hc hleft hℓ hlift hn hG

end InteractingSLE.Sec7.SideC14
