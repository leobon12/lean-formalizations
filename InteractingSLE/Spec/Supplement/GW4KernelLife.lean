/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4Kernel
import InteractingSLE.Spec.Supplement.GW0

/-!
# Theorem GW4: the infinite relative lifetime from GW3's word bounds

Packet PROVE-T14-GW4. Theorem GW4, proof (`source/spec/p625-671.md` L260, p. 639): "The relative endpoint is the
designated `x_C`, hence is infinity in the reversed chart. All cumulative groups are greater than `−2` by GW3. At a
proposed finite relative lifetime, integrated nonexplosion and bounded-coordinate localization would bound the whole
relative hull, contradicting that endpoint. The relative lifetime is infinite."

## Main results

* `ae_lifetime_eq_top_of_counterflowWord` (proved): a centred counterflow whose word (in the inversion chart) has every
  side partial sum greater than `−2` has almost surely infinite lifetime (GW0's backward implication,
  `GW0.ae_lifetime_eq_top_of_neg_two_lt`, integrated nonexplosion);
* `GW3WordBoundStatement` (named input: Lemma GW3's bounds (GW3.2), "`−2 < S_L, S_R ≤ d`");
* `GW4TraversalCoreStatement` (named input: `GW4.GW4TraversalStatement` without its lifetime conjunct);
* **`gw4TraversalStatement_of_core`**: the two give `GW4TraversalStatement`;
* **`componentKernels_of_gw4Core`**: the frozen component-kernel anchor's conclusion from the between-region geometry,
  GW3's field law, GW3's word bounds, GW4's traversal core and Theorems 1.2–1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4

/-- **GW4's lifetime step**: a driver of the angle-`0` flow line at `16/κ` (the centred counterflow in the inversion
chart) whose word has every side partial sum greater than `−2` has almost surely infinite lifetime. -/
theorem ae_lifetime_eq_top_of_counterflowWord {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver (16 / κ) b' J' 0 Q h' W ζ)
    (hL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    (hR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) :
    ∀ᵐ ω ∂Q, ζ ω = ⊤ := by
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  exact GW0.ae_lifetime_eq_top_of_neg_two_lt (Theorem15.isOrderedForceWord_flowLine b' J' 0)
    (fun j _ => hL j) (fun j _ => hR j) hC.1

/-- **Named input: Lemma GW3, the word bounds (GW3.2)** (p. 636: "In the reversed counterflow chart their finite
cumulative words are `S_L = (H_R + πχ)/Λ − 1`, `S_R = (−H_L + πχ)/Λ − 1`, `−2 < S_L, S_R ≤ d`"; proof, p. 637: "Apply
the compatible inversion with the fixed frame `F = −h − πχ` … On a flow flank `H_R = −Λ` or `H_L = Λ`, both formulas
equal `c − 2 = d`. On a lower real connector, its original ambient counterflow sum is `(H_R + πχ)/Λ − 1 > −2` and its
low inequality makes it at most `d`"). Binders and component data of `GW4.GW4TraversalStatement` (verbatim): every
centred counterflow of a component field with a GW3.1 word — read, as in the frozen `IsCenteredCounterflowDriver`, as
the angle-`0` flow line at `16/κ` of the inverted field with some data `b'` — has a word whose side partial sums all
exceed `−2`. -/
def GW3WordBoundStatement : Prop :=
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
          ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞),
            IsPiecewiseConstantBoundaryData b' J' →
            (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
              (QuantumZipper.chiC (16 / κ)) (hC ω) (h' ω)) →
            IsFlowLineDriver (16 / κ) b' J' 0 ν h' WC ζC →
            (∀ i : Fin (flowLineNL b' J' 0),
              -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) ∧
            ∀ i : Fin (flowLineNR b' J' 0),
              -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l

/-- **Named input: Theorem GW4, the component traversal, without the lifetime** (pp. 637–639, "The between-region and
the actual intervals" and "The full kernel and the one phase"): `GW4.GW4TraversalStatement` without its conjunct
`ζC = ⊤`, which `gw4TraversalStatement_of_core` derives from GW3's word bounds. -/
def GW4TraversalCoreStatement : Prop :=
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
            ∀ᵐ ω ∂ν, IsComponentTraversal c.2.1 (fun t => W' t ω) (fun t => WC t ω)

/-- **GW4's traversal statement from its core and GW3's word bounds** (conditional helper with a distinct name): the
relative lifetime is infinite (`ae_lifetime_eq_top_of_counterflowWord`). -/
theorem gw4TraversalStatement_of_core (hT : GW4TraversalCoreStatement.{u}) (hW : GW3WordBoundStatement.{u}) :
    GW4TraversalStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have hT' := hT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE
  have hW' := hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE
  filter_upwards [hT', hW'] with ω₀ hTω hWω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  obtain ⟨WC, ζC, hcd, htrav⟩ := hTω C hCm c hC bC jumpsC hch htr hpc hbd hgff
  obtain ⟨b', J', h', hpc', htr', hfl⟩ := hcd
  obtain ⟨hL, hR⟩ := hWω C hCm c hC bC jumpsC hch htr hpc hbd hgff b' J' h' WC ζC hpc' htr' hfl
  refine ⟨WC, ζC, ⟨b', J', h', hpc', htr', hfl⟩, ?_⟩
  filter_upwards [ae_lifetime_eq_top_of_counterflowWord hfl hL hR, htrav] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **Theorem 1.4, component kernels** (Specification p. 5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, from the finest named inputs of Lemma GW3 and Theorem GW4: the
between-region geometry, GW3's field law, GW3's word bounds, GW4's traversal core, and Theorems 1.2–1.3 (the types
of the frozen anchors). -/
theorem componentKernels_of_gw4Core (hG : GW3.GW3GeometryStatement.{u}) (hF : GW3FieldLawStatement.{u})
    (hWB : GW3WordBoundStatement.{u}) (hT : GW4TraversalCoreStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u})
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
  componentKernels_of_gw4Inputs hG hF (gw4TraversalStatement_of_core hT hWB) h12 h13 hκ hκ4 b jumps hb hh hcf hζ'
    E hE

end GW4

end Theorem14

end InteractingSLE
