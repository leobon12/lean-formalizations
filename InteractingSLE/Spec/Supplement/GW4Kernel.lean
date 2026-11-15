/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem14
import InteractingSLE.Spec.Supplement.GW3Chart
import InteractingSLE.Spec.Exist.StagedKernel
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Sec7.Lemma75Bridge

/-!
# Theorem GW4: the component field–path kernels from GW3's field law, GW4's traversal law and determination

Packet PROVE-T14-GW4. Supplement Theorem GW4 (`source/spec/p625-671.md` L229–L262, pp. 637–639): "Conditional on the
labelled walks, the complete component field–path pairs have the product of the canonical finite-word kernels in
(GW3.2)." The named input `Theorem14.GW4KernelStatement` is the second assertion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, verbatim.

The source proof has four parts, each stated here exactly (same binders as `GW4KernelStatement`):

1. **Lemma GW3, the initial field law** (`GW3FieldLawStatement`, p. 636: "in a common-lift chart … its conditional
   flow-oriented boundary values are (GW3.1) … The zero-boundary fields in the countably many selected components are
   conditionally independent"): for every choice of component charts there are lifts (the inherited ones) in which
   the component fields are, conditionally on the walks, GFFs with the GW3.1 words, and they are independent.
2. **Theorem GW4, the component traversals** (`GW4TraversalStatement`, pp. 637–639, "The between-region and the
   actual intervals", "The full kernel and the one phase", the lifetime paragraph): for one component, a chart with
   the inherited lift and the conditional component field, the actual un-erased traversal has a continuous relative
   driver which, conditionally on the walks, drives the centred counterflow of the component field with infinite
   relative lifetime.
3. **Universal determination** (`CounterflowDeterminationStatement`, p. 639: "Universal determination makes each
   actual complete component traversal a function of its own component field and its recorded initial finite word";
   Theorem 1.2 at `16/κ` in driver form): a centred counterflow driver with infinite lifetime is almost surely a
   measurable function of the field. **Proved** from Theorems 1.2 and 1.3 (the types of the frozen anchors, named
   inputs `Exist.Theorem12Statement`, `Exist.Theorem13Statement`): `counterflowDeterminationStatement_of_thm12`.
4. **The product of the field–path kernels** (p. 639: "Finally, the initial zero-boundary component fields are
   independent by GW3 … This proves the product of full field–path kernels, rather than independence inferred only
   from marginals") — proved here: `iIndepFun_pair_of_ae_eq_comp` and **`gw4KernelStatement_of_inputs`**.

With `GW3Chart` (`gw3ChartStatement_of_geometry`), **`componentKernels_of_gw4Inputs`** gives the frozen
component-kernel anchor's conclusion from the geometry, the two GW3/GW4 inputs and Theorems 1.2–1.3
(`GW4KernelLife` refines the traversal input further).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4

/-! ### The product of the field–path kernels -/

/-- **Independence of field–path pairs from independent fields and determination.** If the fields `X i` are
independent and each path `Y i` is almost surely a measurable function `G i` of its own field, then the pairs
`(X i, Y i)` are independent (GW4, p. 639: "Universal determination makes each actual complete component traversal a
function of its own component field … This proves the product of full field–path kernels"). -/
theorem iIndepFun_pair_of_ae_eq_comp {Ω ι α β : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [MeasurableSpace α] [MeasurableSpace β] {X : ι → Ω → α} {Y : ι → Ω → β} (hX : iIndepFun X μ)
    {G : ι → α → β} (hG : ∀ i, Measurable (G i)) (hY : ∀ i, ∀ᵐ ω ∂μ, Y i ω = G i (X i ω)) :
    iIndepFun (fun i ω => (X i ω, Y i ω)) μ := by
  have h1 : iIndepFun (fun i => (fun x => (x, G i x)) ∘ X i) μ :=
    hX.comp (fun i x => (x, G i x)) fun i => measurable_id.prodMk (hG i)
  refine h1.congr fun i => ?_
  filter_upwards [hY i] with ω hω
  simp only [Function.comp_apply, hω]

/-! ### The named inputs -/

/-- **Named input: Lemma GW3, the initial field law** (p. 636: "Then, in a common-lift chart `(C; x_C, y_C) → (ℍ; 0,
∞)`, its conditional flow-oriented boundary values are (GW3.1) … The real values are the actual original boundary
values, with every original height jump and every actual flow/connector junction retained. The zero-boundary fields in
the countably many selected components are conditionally independent … This is an initial-field assertion and does
not assume a counterflow traversal of `C`"; "Their inherited lifts are the unique ones fixed above", p. 639). Binders
of `GW4KernelStatement` (verbatim): almost surely, for every choice of component charts `cs` there are lifts `ℓ`
(keeping component charts) such that, conditionally on the labelled walks (`ν`), the field read in each chart is a GFF
with a GW3.1 word, and these component fields are independent. -/
def GW3FieldLawStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
          ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens),
            (∀ C ∈ betweenComponents R L,
              IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
              (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
                (hC C ω)) ∧
              ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
                IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                  (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
                IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            iIndepFun (fun (C : betweenComponents R L) ω => hC C ω) ν

/-- **Named input: Theorem GW4, the component traversal** (pp. 637–639: "Each nondegenerate matched Jordan component
has its actual un-erased entry-to-exit counterflow traversal, with continuous relative driver and infinite relative
capacity lifetime. Conditional on the labelled walks, the complete component field–path pairs have … the canonical
finite-word kernels in (GW3.2)"; proof paragraphs "The between-region and the actual intervals", "The full kernel and
the one phase" (Aux. 122 forces `δ_s = 0`), and "The relative endpoint is the designated `x_C` … The relative lifetime
is infinite"). Binders of `GW4KernelStatement` (verbatim): almost surely, for every component `C` between the walks,
every component chart `c` and conditional component field `hC` with a GW3.1 word (the conclusion of
`GW3FieldLawStatement` for `C`), there is a relative driver `WC` that, conditionally on the walks, drives the centred
counterflow of `hC` with infinite lifetime and is the actual un-erased traversal of `C` by the ambient counterflow. -/
def GW4TraversalStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∃ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ ν hC WC ζC ∧
            ∀ᵐ ω ∂ν, ζC ω = ⊤ ∧ IsComponentTraversal c.2.1 (fun t => W' t ω) (fun t => WC t ω)

/-- **Named input: universal determination of the centred counterflow** (GW4, p. 639: "Universal determination makes
each actual complete component traversal a function of its own component field and its recorded initial finite word";
Specification Theorem 1.2 for the counterflow at `16/κ`, in driver form): on any probability space, a centred
counterflow driver of a GFF with piecewise-constant data, with almost surely infinite lifetime, is almost surely a
Borel function of the field. -/
def CounterflowDeterminationStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
    IsPiecewiseConstantBoundaryData bC jumpsC → IsGFFWithBoundaryData Q hC bC jumpsC →
    ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ Q hC W ζ → (∀ᵐ ω ∂Q, ζ ω = ⊤) →
      ∃ G : LQGMetric.DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ), Measurable G ∧
        ∀ᵐ ω ∂Q, (fun t => W t ω) = G (hC ω)

/-! ### Universal determination from Theorems 1.2 and 1.3 -/

/-- **Universal determination of the centred counterflow from Theorems 1.2–1.3** (both at universe `u`, as the named
inputs `Exist.Theorem12Statement` and `Exist.Theorem13Statement`, i.e. exactly the types of the frozen anchors). The
counterflow coupling field is a Borel function of the field (`chartTransport` in the inversion chart, then
`flowField`); Theorem 1.2 at `16/κ` gives the determined trace `Φ`; PROVE-STAGED's decoding
(`Exist.Staged.ae_detCode_eq`, with Theorem 1.3) writes the killed driver as `drvPath (detCode Φ (word, field))` before
the lifetime, here `∞`. -/
theorem counterflowDeterminationStatement_of_thm12 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : CounterflowDeterminationStatement.{u} := by
  intro κ hκ _ Ω _ Q _ hC bC jumpsC _ _ W ζ hcd hζ
  obtain ⟨b', jumps', h', -, htr, hfl⟩ := hcd
  obtain ⟨h'', 𝓕, VL, VR, B, htr', hcoup⟩ := hfl
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hc := Chart.isConformal_infinitySourceChart
  have hℓ := Chart.locallyIntegrableOn_of_continuousOn isDomainChart_infinitySourceChart.continuousOn_lift_inv
  set T : LQGMetric.DistOn upperHalfPlaneOpens → LQGMetric.DistOn upperHalfPlaneOpens := fun x =>
    Exist.flowField 0 (0 * QuantumZipper.chiC (16 / κ))
      (Chart.chartTransport hc (-1) (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) x) with hTdef
  have hT : Measurable T := (Exist.measurable_flowField _ _).comp (Chart.measurable_chartTransport hc _ _ _)
  have hh'' : ∀ ω, h'' ω = T (hC ω) := fun ω => by
    rw [Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr' ω), (htr ω).eq_chartTransport hc hℓ]
  have hF := Theorem15.isOrderedForceWord_flowLine b' jumps' 0
  obtain ⟨Φ, hΦm, hΦ⟩ := h12 (16 / κ) hκ' _ _ _ _ hF hcoup
  set Φ' : Exist.Staged.WordData (flowLineNL b' jumps' 0) (flowLineNR b' jumps' 0) ×
      LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ) := fun p => Φ p.2 with hΦ'def
  have hΦ'm : Measurable Φ' := hΦm.comp measurable_snd
  set wd : Exist.Staged.WordData (flowLineNL b' jumps' 0) (flowLineNR b' jumps' 0) :=
    ((flowLineXL b' jumps' 0, flowLineXR b' jumps' 0),
      (flowLineRhoL (16 / κ) b' jumps' 0 0, flowLineRhoR (16 / κ) b' jumps' 0 0)) with hwd
  have hdet := Exist.Staged.ae_detCode_eq hκ' (Φ := Φ') hF h13 hcoup hΦ
  refine ⟨fun x => Exist.Staged.drvPath (Exist.Staged.detCode Φ' (wd, T x)),
    Exist.Staged.measurable_drvPath.comp ((Exist.Staged.measurable_detCode hΦ'm).comp
      (measurable_const.prodMk hT)), ?_⟩
  filter_upwards [hdet, hζ] with ω hω hζω
  obtain ⟨x₀, -, hζx, hw, hcode⟩ := hω
  funext t
  have ht : (t : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
  change W t ω = Exist.Staged.drvPath (Exist.Staged.detCode Φ' (wd, T (hC ω))) t
  rw [← hh'' ω, hcode, (Exist.Staged.drvPath_dOf_agree x₀).2 t (hζx ▸ ht)]
  exact ((hw t ht).1).symm

/-! ### Theorem GW4 from the named inputs -/

/-- **Theorem GW4, the component kernels, from GW3's field law, GW4's traversal law and universal determination**
(conditional helper with a distinct name). For each component the traversal law is applied in the chart with the
inherited lift; determination writes each traversal driver as a Borel function of its own component field, so the
independence of the component fields (GW3) gives the independence of the field–path pairs
(`iIndepFun_pair_of_ae_eq_comp`). -/
theorem gw4KernelStatement_of_inputs (hF : GW3FieldLawStatement.{u}) (hT : GW4TraversalStatement.{u})
    (hD : CounterflowDeterminationStatement.{u}) : GW4KernelStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have hF' := hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE
  have hT' := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE
  filter_upwards [hF', hT'] with ω₀ hFω hTω
  intro R L ν cs hcs
  obtain ⟨ℓ, hC, hC1, hind⟩ := hFω cs hcs
  have hT1 : ∀ C ∈ betweenComponents R L, ∃ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ ν (hC C) WC ζC ∧
        ∀ᵐ ω ∂ν, ζC ω = ⊤ ∧ IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC t ω) := by
    intro C hCm
    obtain ⟨hch, htr, bC, jumpsC, hpc, hbd, hgff⟩ := hC1 C hCm
    exact hTω C hCm ((cs C).1, (cs C).2.1, ℓ C) (hC C) bC jumpsC hch htr hpc hbd hgff
  choose! WC ζC hWC using hT1
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  have hdet : ∀ C ∈ betweenComponents R L, ∃ G : LQGMetric.DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ),
      Measurable G ∧ ∀ᵐ ω ∂ν, (fun t => WC C t ω) = G (hC C ω) := by
    intro C hCm
    obtain ⟨-, -, bC, jumpsC, hpc, -, hgff⟩ := hC1 C hCm
    exact hD κ hκ hκ4 ν (hC C) bC jumpsC hpc hgff (WC C) (ζC C) (hWC C hCm).1
      ((hWC C hCm).2.mono fun ω hω => hω.1)
  choose! G hGm hGae using hdet
  refine ⟨ℓ, hC, WC, ζC, fun C hCm => ?_, ?_⟩
  · obtain ⟨hch, htr, hgff⟩ := hC1 C hCm
    exact ⟨hch, htr, hgff, (hWC C hCm).1, (hWC C hCm).2⟩
  · exact iIndepFun_pair_of_ae_eq_comp (X := fun (C : betweenComponents R L) ω => hC C ω)
      (Y := fun (C : betweenComponents R L) ω => fun t => WC C t ω) (G := fun C => G C.1) hind
      (fun C => hGm C.1 C.2) fun C => hGae C.1 C.2

/-- **Theorem GW4, the component kernels, from GW3's field law, GW4's traversal law and Theorems 1.2–1.3.** -/
theorem gw4KernelStatement_of_thm12 (hF : GW3FieldLawStatement.{u}) (hT : GW4TraversalStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) : GW4KernelStatement.{u} :=
  gw4KernelStatement_of_inputs hF hT (counterflowDeterminationStatement_of_thm12 h12 h13)

/-- **Theorem 1.4, component kernels** (Specification p. 5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, from the four named inputs of Lemma GW3 and Theorem GW4: the
between-region geometry (`GW3Chart.GW3GeometryStatement`), GW3's field law, GW4's traversal law, and Theorems 1.2
and 1.3 (the types of the frozen anchors, for universal determination). -/
theorem componentKernels_of_gw4Inputs (hG : GW3.GW3GeometryStatement.{u}) (hF : GW3FieldLawStatement.{u})
    (hT : GW4TraversalStatement.{u}) (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec)) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  componentKernels_of_inputs (GW3.gw3ChartStatement_of_geometry hG) (gw4KernelStatement_of_thm12 hF hT h12 h13)
    hκ hκ4 b jumps hb hh hcf hζ' E hE

end GW4

end Theorem14

end InteractingSLE
