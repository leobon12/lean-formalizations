/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRoute
import InteractingSLE.Spec.Sec5.Prop513FieldAssembly
import InteractingSLE.Spec.Sec7.StripPocketPathFinal

/-!
# The strip counterflows' no-return without the general no-return input

Packet PROVE-CFNORETURN3 (ruling R59). Two consumers on the route of Theorems 1.2–1.3 take
`Theorem14.GW4Ident.CounterflowNoReturnStatement` (or its pathwise form) as an input, although their counterflow words
are admissible at `κ′ = 16/κ`, so Aux. lemma 7 at `16/κ` alone gives the no-return
(`CfNoReturn.Route.ae_trace_ne_zero_of_isFlowLineDriver`):

* **Proposition 5.13's strip counterflow** (PROVE-PROP513C, `Sec5.stripCounterflow_trace_mem_H_of_stripGFF`): its
  word is admissible by `Sec5.exists_admissible_stripCounterflowDriver`. `stripCounterflow_noReturn_of_aux7` and
  `stripCounterflow_trace_mem_H_of_stripGFF_of_partA` replace the input by Zhan's Part A inputs at `16/κ`.
* **Lemma 7.25's pocket word from the strip system** (PROVE-STRIPSYS31,
  `Sec7.StripPocketPath.pocketWordEvolution_of_stripSystem`, input `hnohit`): the strip system's heights `hcumL`,
  `hcumR` at the angles `∓π/2` are the barrier bounds of `CfNoReturn.Route.ae_trace_ne_zero_of_centered`, so `hnohit`
  follows from `haux7`, which the theorem already takes (`ae_noReturn_counterflow`,
  `pocketWordEvolution_of_stripSystem_without_nohit`).

No result here uses Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement`, `Theorem13Statement`, two-seed completeness
or Lemma 7.25 (R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE

/-! ### Proposition 5.13's strip counterflow -/

namespace Sec5

open Sec4

/-- **Proposition 5.13's strip counterflow does not return to its start** (from Aux. lemma 7 at `16/κ`): its word is
admissible (`exists_admissible_stripCounterflowDriver`), so both seeds are barriers. -/
theorem stripCounterflow_noReturn_of_aux7 {κ x₀ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ)) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hG : IsStripGFF κ P h bL bU JL JU)
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  have hcanon := Prop513Field.canonicalFieldStatement (x₀ := x₀) hκ hdata.1 hdata.2.1 hG
  obtain ⟨b', J', h', _, hfl, hadm⟩ := exists_admissible_stripCounterflowDriver hκ hdata hcf hcanon
  exact CfNoReturn.Route.ae_trace_ne_zero_of_isFlowLineDriver hκ' haux7 hfl hadm

/-- **The strip trace input from the original strip GFF and Aux. lemma 7 at `16/κ`**:
`stripCounterflow_trace_mem_H_of_stripGFF` with the centred no-return input discharged. -/
theorem stripCounterflow_trace_mem_H_of_stripGFF_of_aux7 {κ x₀ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ)) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hG : IsStripGFF κ P h bL bU JL JU)
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H := by
  have hcanon := Prop513Field.canonicalFieldStatement (x₀ := x₀) hκ hdata.1 hdata.2.1 hG
  exact ae_stripCounterflow_lifetime_eq_top_and_trace_mem_H hκ hdata hcf hcanon
    (stripCounterflow_noReturn_of_aux7 hκ hκ4 haux7 hdata hG hcf)

/-- **The strip trace input from the original strip GFF and Zhan's Part A inputs at `16/κ`**
(`PartAInputsSixteenDiv`): it replaces `stripCounterflow_trace_mem_H_of_stripGFF` (input
`CounterflowNoReturnStatement`) on the route of Theorems 1.2–1.3. -/
theorem stripCounterflow_trace_mem_H_of_stripGFF_of_partA (hA : PartAInputsSixteenDiv) {κ x₀ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hG : IsStripGFF κ P h bL bU JL JU)
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H :=
  stripCounterflow_trace_mem_H_of_stripGFF_of_aux7 hκ hκ4 (aux7Statement_sixteen_div_of_partA hA hκ hκ4) hdata hG hcf

end Sec5

/-! ### The strip system's counterflow (Lemma 7.25's pocket word) -/

namespace Sec7.StripPocketPath

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling StripSideHeightProb
open Exist.Staged (IsRegularDriver)

section NoReturn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The strip system's counterflow does not return to its seed** (`hnohit` of `pocketWordEvolution_of_stripSystem`,
ruling R59), from Aux. lemma 7 at `κ′ = 16/κ`: Aux. lemma 130's heights at the angles `∓π/2` are the barrier bounds
of `CfNoReturn.Route.ae_trace_ne_zero_of_centered`. Every version `η` of the trace avoids `0` at positive times. -/
theorem ae_noReturn_counterflow (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0 := by
  have hno := CfNoReturn.Route.ae_trace_ne_zero_of_centered hS.kappa_pos hS.kappa_lt_four haux7 hS.boundaryData
    (fun x hx hxJ => by have := hcumL _ StripSys.neg_pi_div_two_mem_Icc x hx hxJ; linarith)
    (fun x hx hxJ => by have := hcumR _ StripSys.pi_div_two_mem_Icc x hx hxJ; linarith) hS.gff hS.counterflow
  filter_upwards [hno, hηtr] with ω hω hη t ht
  have h1 := hω _ hη t.toNNReal (Real.toNNReal_pos.2 ht)
  rwa [Real.coe_toNNReal _ ht.le] at h1

/-- **hPW from the strip system without the no-return input** (Aux. lemma 130 and Lemma 7.25's proof, pp. 408–414):
`pocketWordEvolution_of_stripSystem` with `hnohit` discharged by `ae_noReturn_counterflow` from `haux7`, which the
theorem already takes. Every other input is unchanged. -/
theorem pocketWordEvolution_of_stripSystem_without_nohit {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    {rL rR : ℝ} (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4) (hRr : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hregα : ∀ j ω, IsRegularDriver (Es (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (Es (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω)) (h𝓦 : 𝓦 ≤ mΩ)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable[𝓦] fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.alphaSpec θ₁) 0 ω).1 1
      (Es (StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0)
    (hLm : ∀ q t, Measurable[𝓦] fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 0 ω).1
      (StripSys.rt q) (Es (StripSys.betaSpec (StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω)))
    (hwit : ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂)
    (hwitI : ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (𝔥 : DistOn upperHalfPlaneOpens)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      PocketUnionPtInput κ rL rR (𝓦 ⊔ Ito.nullSets P) P α (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥 ∧
        PocketUnionPtInputInf κ rL rR (𝓦 ⊔ Ito.nullSets P) P α (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥) :
    Lemma725Ref.PocketWordEvolution.{u} (16 / κ) rL rR :=
  pocketWordEvolution_of_stripSystem h44 haux7 hS hcumL hcumR hθ₁ hθ₂ hL hLd hRr hRd hregα hregβ hregE h𝓦 hαc hα0
    hαm hαtr hβc hβ0 hβm hβtr hLc hL0 hLm hLtr hηc hηH hη0 hηm hηtr hwalls hwallsL
    (ae_noReturn_counterflow haux7 hS hcumL hcumR hηtr) hav hwit hwitI hh₀ 𝔥 hin

end NoReturn

end Sec7.StripPocketPath

end InteractingSLE
