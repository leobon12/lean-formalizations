/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37WallsStrip
import InteractingSLE.Spec.Sec7.R7OuterAvoid
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRouteStrip

/-!
# Pocket-word wall inputs from the strip system

PROVE-POCKET-WORDIN. Adapt the landed determination/locality and nonboundary
duality results to the rational wall family. `positiveSeed` only fills the unused
nonpositive indices with the already constructed wall at seed one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.PocketWordIn

open StripWall StripSideHeightProb StripPocketPath WangWu
open Exist.Staged (IsRegularDriver)

/-- Complete the positive rational index set by using seed one at nonpositive indices. -/
def positiveSeed (q : ℚ) : ℚ := if 0 < q then q else 1

theorem positiveSeed_pos (q : ℚ) : 0 < positiveSeed q := by
  unfold positiveSeed
  split_ifs with hq
  · exact hq
  · exact zero_lt_one

theorem positiveSeed_of_pos {q : ℚ} (hq : 0 < q) : positiveSeed q = q :=
  ite_eq_left hq

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- Determination and entrance-history locality at one positive rational seed.
The four conclusions are precisely the corresponding inputs of the per-seed assembly. -/
theorem wall_inputs (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : StripSys.IsStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) {q : ℚ} (hq : 0 < q)
    (hr : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hl : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    {α L : Ω → ℝ≥0 → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hvL : IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) L) :
    (∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P ∧
    (∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    Sec6.IsEntranceHistoryLocal L (WholeField.centredField h u₀) P := by
  have hw := Aux37Walls.lemma62_walls_rat h44 hS hleft hright hθ₁ hθ₂ hq hr hl hu₀
    hvL.continuous hvL.zero hvL.measurable hvL.ae_isGeneratingTrace
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace
  exact ⟨hw.2.2.1, hw.2.2.2.1, hw.1, hw.2.1⟩

/-- The completed left-wall family exists using only the already proved strip versions.
At every positive index this is the original prescribed two-angle program. -/
theorem exists_wall_family (hS : StripSys.IsStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω)) :
    ∃ Lr : ℚ → Ω → ℝ≥0 → ℂ, ∀ q,
      IsWallVersion P (E (StripSys.betaSpec (StripSys.rt (positiveSeed q)) θ₂))
        (StripSys.rt (positiveSeed q)) (Lr q) := by
  have hex := fun q => exists_isWallVersion_beta hS hleft hright hθ₂
    (StripSys.rt (positiveSeed q)) (hl _ (positiveSeed_pos q))
  choose Lr hLr using hex
  exact ⟨Lr, fun q => (hLr q).1⟩

/-- Rational-time avoidance follows from Proposition 4.11 for the unchanged extremal flow.
No full-generality determination or trace theorem is used. -/
theorem ae_avoidance (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (hS : StripSys.IsStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {β : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) →
      negInv (η ω q) ∉ leftSideOf (range (β ω)) := by
  obtain ⟨hf, F, VL, VR, B, ht, hC⟩ := isFlowLineDriver_leftExtremal
    hS.kappa_pos hS.boundaryData hS.gff hS.isStagedHistory_leftExtremal
  have hβ : IsFlowLine κ b J 0 (π / 2) P h β
      (fun ω => (E StripSys.leftExtremalSpec 0 ω).2) := by
    refine ⟨hf, F, fun t ω => (E StripSys.leftExtremalSpec 0 ω).1 t,
      VL, VR, B, ht, hC, ?_⟩
    filter_upwards [hβtr, ae_simple_trace_leftExtremal_strip hS hleft hright]
      with ω htr hreg
    simpa only [hreg.1, Complex.ofReal_zero, sub_zero] using htr
  have hav := R7Outer.ae_negInv_trace_notMem_leftSideOf h411 hS.kappa_pos hS.kappa_lt_four
    hS.boundaryData (heights_pi_div_two hS.kappa_pos hS.kappa_lt_four hleft hright)
    hS.gff hS.counterflow hβ
  filter_upwards [hav, hS.lifetime, hηtr] with ω ha hζ hη q hq
  have ha' := ha hζ _ hη (q : ℝ).toNNReal
  rwa [Real.coe_toNNReal _ hq] at ha'

end InteractingSLE.Sec7.PocketWordIn
