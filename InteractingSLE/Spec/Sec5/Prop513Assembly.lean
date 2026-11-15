/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513
import InteractingSLE.Spec.Sec5.Prop513Trace
import InteractingSLE.Spec.Sec5.Prop513Tree
import InteractingSLE.Spec.Sec5.Lemma57Cap

/-!
# Proposition 5.13 from a represented extreme-angle tree and the tip inputs

Packet PROVE-PROP513C. These are conditional assembly helpers, not replacements
for a source theorem. Node and cone measurability are discharged from the
countable path representation. For strip counterflows, lifetime and strict
half-plane membership are also discharged, conditional on canonical field
transport and the separate strip no-return assertion. Proposition 5.9's two tip
assertions and Lemma 5.7's visits and reverse order remain explicit inputs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5

open QuantumZipper Sec4

/-- Lemma 5.7 in the E chart gives the visits of the nodes and the strict
reverse order of all post-terminal descendant points in the capacity chart.
In particular, the root itself is excluded from the strict-order premise. -/
theorem ae_tree_hits_and_order_of_lemma57 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {q : ℝ} (hq : 0 < q)
    {γ : Ω → ℝ≥0 → ℂ} {η : ℕ → Ω → ℝ → ℂ}
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (hτ : ∀ n, 0 < τ n)
    (hroot : ∀ n m ω, η (d n m) ω (τ n) = η n ω (τ n))
    (hγ0 : ∀ᵐ ω ∂P, γ ω 0 = 0)
    (hγH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H)
    (hη : ∀ᵐ ω ∂P, ∀ n, η n ω 0 = 0 ∧ ∀ t : ℝ, 0 < t → η n ω t ∈ H)
    (h57 : ∀ᵐ ω ∂P, ∀ n, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ τ n →
      ∃ u ∈ Icc (0 : ℝ) 1, stripCounterflowPath q (γ ω) u = η n ω t ∧
        ∀ r ∈ Icc (0 : ℝ) u, stripCounterflowPath q (γ ω) r ≠ η n ω s) :
    let ξ := fun n ω t => (stripCounterflowChart q).1 (η n ω t)
    ∀ᵐ ω ∂P,
      (∀ n, ∃ t, γ ω t = extremeAngleTreeNode ξ τ n ω) ∧
      ∀ n, ∀ p ∈ extremeAngleTreeDescendants ξ τ d n ω,
        ∃ v, γ ω v = p ∧ ∀ w ≤ v, γ ω w ≠ extremeAngleTreeNode ξ τ n ω := by
  dsimp only
  filter_upwards [hγ0, hγH, hη, h57] with ω hγ0ω hγω hηω h57ω
  have ho := fun n (s t : ℝ) => lemma57_reverseOrder_capacityChart hq hγ0ω hγω
    (hηω n).1 (hηω n).2 (h57ω n) (s := s) (t := t)
  constructor
  · intro n
    obtain ⟨v, hv, _⟩ := ho n 0 (τ n) le_rfl (hτ n) le_rfl
    exact ⟨v, hv⟩
  · intro n p hp
    obtain ⟨m, t, ht, rfl⟩ := mem_iUnion.1 hp
    obtain ⟨v, hv, hav⟩ := ho (d n m) (τ n) t (hτ n).le ht.1 ht.2
    refine ⟨v, hv, ?_⟩
    intro w hw
    simpa only [hroot n m ω, extremeAngleTreeNode] using hav w hw

/-- Prop. 5.13 for a represented extreme-angle tree. The node and cone
measurability hypotheses of `prop513_path_of_tips` are proved from the paths. -/
theorem prop513_path_of_tree_tips {k : ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hk : 4 < k)
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {𝒢 : MeasurableSpace Ω}
    {γ : Ω → ℝ≥0 → ℂ} {η : ℕ → Ω → ℝ → ℂ}
    (hηm : ∀ n t, Measurable[𝒢] fun ω => η n ω t)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (hτ : ∀ n m, τ n ≤ τ (d n m))
    (hroot : ∀ n m ω, η (d n m) ω (τ n) = extremeAngleTreeNode η τ n ω)
    (hηc : ∀ n m ω, ContinuousOn (η (d n m) ω) (Icc (τ n) (τ (d n m))))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (htrH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H)
    (hzγ : ∀ᵐ ω ∂P, ∀ n, ∃ t, γ ω t = extremeAngleTreeNode η τ n ω)
    (hord : ∀ᵐ ω ∂P, ∀ n, ∀ p ∈ extremeAngleTreeDescendants η τ d n ω,
      ∃ v, γ ω v = p ∧ ∀ w ≤ v, γ ω w ≠ extremeAngleTreeNode η τ n ω)
    (htip : ∀ n, ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P,
      (q : ℝ) < traceFirstVisit (γ ω) (extremeAngleTreeNode η τ n ω) →
        γ ω (q : ℝ).toNNReal ∈ extremeAngleTreeCone η τ d n ω)
    (htip0 : ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P,
      γ ω (q : ℝ).toNNReal ∈ closure (range fun n => extremeAngleTreeNode η τ n ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  exact @prop513_path_of_tips k nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ
    hk hE hζ 𝒢 γ (extremeAngleTreeNode η τ) (extremeAngleTreeDescendants η τ d)
    (extremeAngleTreeCone η τ d) (measurable_extremeAngleTreeNode hηm τ)
    (measurable_extremeAngleTreeCone hηm τ d hτ hroot hηc) (fun _ _ => rfl)
    htr htrH hzγ hord htip htip0

/-- Strip form of the assembly, with lifetime and boundary avoidance derived
from the canonical heights. Its remaining field-transport, no-return, tree-path,
Lemma 5.7 and Proposition 5.9 inputs are displayed in its type. -/
theorem prop513_path_of_stripCounterflow_tree_tips {κ x₀ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ)
    (hcanon : StripCounterflowCanonicalFieldStatement κ x₀ bL bU P h)
    (hzero : ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0)
    {𝒢 : MeasurableSpace Ω} {γ : Ω → ℝ≥0 → ℂ} {η : ℕ → Ω → ℝ → ℂ}
    (hηm : ∀ n t, Measurable[𝒢] fun ω => η n ω t)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (hτ : ∀ n m, τ n ≤ τ (d n m))
    (hroot : ∀ n m ω, η (d n m) ω (τ n) = extremeAngleTreeNode η τ n ω)
    (hηc : ∀ n m ω, ContinuousOn (η (d n m) ω) (Icc (τ n) (τ (d n m))))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hzγ : ∀ᵐ ω ∂P, ∀ n, ∃ t, γ ω t = extremeAngleTreeNode η τ n ω)
    (hord : ∀ᵐ ω ∂P, ∀ n, ∀ p ∈ extremeAngleTreeDescendants η τ d n ω,
      ∃ v, γ ω v = p ∧ ∀ w ≤ v, γ ω w ≠ extremeAngleTreeNode η τ n ω)
    (htip : ∀ n, ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P,
      (q : ℝ) < traceFirstVisit (γ ω) (extremeAngleTreeNode η τ n ω) →
        γ ω (q : ℝ).toNNReal ∈ extremeAngleTreeCone η τ d n ω)
    (htip0 : ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P,
      γ ω (q : ℝ).toNNReal ∈ closure (range fun n => extremeAngleTreeNode η τ n ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have hreg := @ae_stripCounterflow_lifetime_eq_top_and_trace_mem_H κ x₀ hκ bL bU JL JU
    hdata Ω mΩ P _ h W ζ hcf hcanon hzero
  obtain ⟨b', J', h', _, hfl, _⟩ :=
    @exists_admissible_stripCounterflowDriver κ x₀ hκ bL bU JL JU hdata Ω mΩ P _ h W ζ hcf hcanon
  obtain ⟨h'', 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hk : 4 < 16 / κ := (lt_div_iff₀ hκ).2 (by linarith only [hκ4])
  have hζ := hreg.mono fun _ hω => hω.1
  have hH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H := by
    filter_upwards [hreg, htr] with ω hω hγω
    exact hω.2 _ hγω
  exact @prop513_path_of_tree_tips (16 / κ) _ _ _ _ _ _ Ω mΩ P _ 𝓕 W VL VR B ζ
    hk hC.1 hζ 𝒢 γ η hηm τ d hτ hroot hηc htr hH hzγ hord htip htip0

end InteractingSLE.Sec5
