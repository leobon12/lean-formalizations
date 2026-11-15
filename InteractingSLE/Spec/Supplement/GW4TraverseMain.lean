/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4TraverseField
import InteractingSLE.Spec.Supplement.GW4TraverseTrace
import InteractingSLE.Spec.Supplement.GW3LawEvery

/-!
# Theorem GW4: the component traversal core from the relative hulls

Packet PROVE-T14-GW4T. `GW4.GW4TraversalCoreStatement` (PROVE-T14-GW4) asks, almost surely over the two boundary walks
and for every between-component `C` with a component chart `c`, for a centred counterflow `(W_C, ζ_C)` of the
component field `h_C` under the conditional law `ν` given the walks, such that `ν`-almost surely the ambient counterflow
traverses `C` as that counterflow (frozen `IsComponentTraversal`).

Here it is reduced to one named statement of the source's traversal analysis, `GW4RelativeHullStatement`, together
with inputs already named in the Theorem 1.4 campaign:

* **`GW4RelativeHullStatement`** (named input; Theorem GW4's proof, pp. 637–639, "The between-region and the actual
  intervals" and "The full kernel and the one phase"): every centred counterflow `W_C` of the component field with
  infinite lifetime generates, `ν`-almost surely, the relative hulls of the ambient traversal: for a continuous
  strictly increasing clock `T` (relative time `s ↦` ambient time `T s`), `K^{W_C}_s = Φ(K'_{T s} ∩ R⁻¹(C))`, where
  `Φ = R ∘ fwd ∘ R` is the component chart read in the ambient counterflow chart `R(z) = −1/z` (the source's
  `D_s ∩ C = E_s`); the ambient trace avoids `closure C` before the entry `T 0` ("Before `τ` no boundary point of `C`
  other than its entry can be visited"); neither tip is at its chart's infinity at positive relative times;
* `GW3Word.BetweenComponentsOpenStatement` (the components are open; from `GW3.GW3GeometryStatement`);
* `GW4.GW3WordBoundStatement` (Lemma GW3's word bounds, giving the infinite relative lifetime);
* Theorems 1.2 and 1.3 (the frozen anchors' types), for the canonical counterflow of the component field
  (`GW4Traverse.cfDrv`) and for complete traces. Theorem GW4 serves Theorem 1.4 only (R43, R48: nothing here feeds
  the inputs of Theorems 1.2–1.3).

## Main results

* **`gw4TraversalCoreStatement_of_relHulls`**: `GW4.GW4TraversalCoreStatement` from the inputs above (the witness is
  the canonical counterflow `cfDrv`, `isCenteredCounterflowDriver_cfDrv`; the traversal is
  `isComponentTraversal_of_relHulls`);
* **`componentKernels_of_relHulls`**: the frozen component-kernel anchor's conclusion (binders verbatim) with
  `GW4TraversalCoreStatement` replaced by these inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Traverse

/-- **Named input: Theorem GW4, the relative hulls of the component traversal** (pp. 637–639). Binders and component
data of `GW4.GW4TraversalCoreStatement` (verbatim). For every centred counterflow `(W_C, ζ_C)` of the component field
under the conditional law `ν` with almost surely infinite lifetime, `ν`-almost surely there is a continuous strictly
increasing clock `T` such that
* before the entry time `T 0` the ambient tip (read in `ℍ` through `R(z) = −1/z`) is not in `closure C`;
* for every relative time `s`, the hull of `W_C` at `s` is the chart image `Φ(K'_{T s} ∩ R⁻¹(C))` of the part of the
  ambient counterflow hull inside the component (`Φ = relMapC c`, `R⁻¹(C) = relDom C`; source: "at every nonterminal
  traversal stop `D_s ∩ C = E_s`", "the continuous-trace criterion gives the actual relative continuous driver and its
  adapted strictly increasing clock", "That lemma forces `δ_s = 0` and identifies the canonical integrated
  finite-word system");
* at positive relative times neither tip is at its chart's infinity (`0` in the counterflow charts).

Compared with `GW4.GW4TraversalCoreStatement`, the existence and law of the component counterflow, its infinite
lifetime, its complete trace and the passage from hulls to the frozen trace form of `IsComponentTraversal` are not
asked: they are proved (`gw4TraversalCoreStatement_of_relHulls`). -/
def GW4RelativeHullStatement : Prop :=
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
          ∀ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ ν hC WC ζC →
            (∀ᵐ ω ∂ν, ζC ω = ⊤) →
            ∀ᵐ ω ∂ν, ∃ T : ℝ≥0 → ℝ≥0, StrictMono T ∧ Continuous T ∧
              (∀ t : ℝ≥0, t < T 0 → ∀ p : ℂ,
                Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) t) (𝓝[H] 0) (𝓝 p) →
                p ≠ 0 → -p⁻¹ ∉ closure C) ∧
              (∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal ω) s =
                relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) (T s) ∩ relDom C)) ∧
              ∀ s : ℝ≥0, 0 < s →
                (∀ p : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) (T s)) (𝓝[H] 0)
                  (𝓝 p) → p ≠ 0) ∧
                ∀ q : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => WC r.toNNReal ω) s) (𝓝[H] 0) (𝓝 q) →
                  q ≠ 0

/-- A between-component lies in `ℍ`. -/
theorem subset_H_of_mem_betweenComponents {R L C : Set ℂ} (hC : C ∈ betweenComponents R L) : C ⊆ H := by
  obtain ⟨z, -, -, -, rfl⟩ := hC
  exact (connectedComponentIn_subset _ _).trans sdiff_subset

/-- **Theorem GW4's traversal core from the relative hulls** (conditional helper with a distinct name). The witness is
the canonical counterflow of the component field (`cfDrv`); its law is `isCenteredCounterflowDriver_cfDrv`, its
infinite lifetime GW3's word bounds (`GW4.ae_lifetime_eq_top_of_counterflowWord`), its complete transient trace
Theorem 1.3, and the traversal `isComponentTraversal_of_relHulls`. -/
theorem gw4TraversalCoreStatement_of_relHulls (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Word.BetweenComponentsOpenStatement.{u})
    (hWB : GW4.GW3WordBoundStatement.{u}) (hH : GW4RelativeHullStatement.{u}) :
    GW4.GW4TraversalCoreStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hO' := hO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE
  have hW' := hWB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE
  have hH' := hH κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ')
  filter_upwards [hO', hW', hH', hamb] with ω₀ hOω hWω hHω hambω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  have hcd := isCenteredCounterflowDriver_cfDrv h12p hκ bC jumpsC h13 hpc hgff
  refine ⟨_, _, hcd, ?_⟩
  obtain ⟨b', J', h', hpc', htr', hfl⟩ := id hcd
  obtain ⟨hL, hR⟩ := hWω C hCm c hC bC jumpsC hch htr hpc hbd hgff b' J' h' _ _ hpc' htr' hfl
  have hζC := GW4.ae_lifetime_eq_top_of_counterflowWord hfl hL hR
  have htrC := ae_trace_of_isCenteredCounterflowDriver h13 hκ hcd hζC
  have hHull := hHω C hCm c hC bC jumpsC hch htr hpc hbd hgff _ _ hcd hζC
  have hCo : IsOpen C := hOω C hCm
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hCm
  filter_upwards [hambω, htrC, hHull] with ω hambω' htrCω hHullω
  obtain ⟨hW'c, hW'0, γ, hγ, -⟩ := hambω'
  obtain ⟨hWCc, hWC0, Γ, hΓ, hΓt⟩ := htrCω
  obtain ⟨T, hT, hTc, hent, hK, hne⟩ := hHullω
  have hdense := dense_of_transientDenseQ (Supp8.GB6.transientDenseQ_of_isGeneratingTrace hΓ hWCc hWC0 hΓt)
  have htipA : ∀ t : ℝ≥0, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) t) (𝓝[H] 0)
      (𝓝 (γ t)) := fun t =>
    IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hW'c.continuousOn hW'0 ENNReal.coe_lt_top
  have htipC : ∀ s : ℝ≥0, Tendsto (QuantumZipper.fwdMapInv
      (fun r : ℝ => (cfDrv h12p hκ bC jumpsC (hC ω)).1 r.toNNReal) s) (𝓝[H] 0) (𝓝 (Γ s)) := fun s =>
    IsGeneratingTrace.tendsto_fwdMapInv_tip hΓ hWCc.continuousOn hWC0 ENNReal.coe_lt_top
  exact isComponentTraversal_of_relHulls hch hCo hCH hW'c hW'0 hγ hWCc hWC0 hΓ hdense hT hTc
    (fun t ht hγt => hent t ht (γ t) (htipA t) hγt) hK
    (fun s hs => ⟨(hne s hs).1 _ (htipA (T s)), (hne s hs).2 _ (htipC s)⟩)

/-- **Theorem 1.4, component kernels** (Specification p. 5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, from the finest named inputs of Lemma GW3 and Theorem GW4 after this
packet: the between-region geometry, GW3's one-chart field law, the walks' no-common-continuum and connector-side
facts, GW0's forward implication, GW4's relative hulls, and Theorems 1.2–1.3 (the types of the frozen anchors). -/
theorem componentKernels_of_relHulls (hG : GW3.GW3GeometryStatement.{u})
    (hF1 : GW3Law.GW3FieldLawOneChartStatement.{u}) (hN : GW3Law.WalkNoCommonContinuumStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hS : GW3Word.WalkConnectorSideStatement.{u})
    (hH : GW4RelativeHullStatement.{u}) (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
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
  GW3Law.componentKernels_of_oneChart hG hF1 hN hGW0 hS
    (gw4TraversalCoreStatement_of_relHulls h12 h13 (GW3Word.betweenComponentsOpenStatement_of_geometry hG)
      (GW3Word.gw3WordBoundStatement_of_inputs (GW3Word.betweenComponentsOpenStatement_of_geometry hG) hGW0 hS) hH)
    h12 h13 hκ hκ4 b jumps hb hh hcf hζ' E hE

/-! ### The two halves of the relative-hull statement -/

/-- **Named input: Theorem GW4, the pathwise relative chain** ("The between-region and the actual intervals",
pp. 637–638: "at every nonterminal traversal stop `D_s ∩ C = E_s` […] The continuous-trace criterion gives the actual
relative continuous driver and its adapted strictly increasing clock. No old excursion is erased"). Binders and
component data of `GW4RelativeHullStatement`. `ν`-almost surely the ambient traversal of `C` has a continuous relative
driver `W_rel` from `0` and a continuous strictly increasing clock `T` with the entry clause, the relative hulls
`K^{W_rel}_s = Φ(K'_{T s} ∩ R⁻¹(C))`, and neither tip at its chart's infinity at positive relative times. No law is
asserted: this is the deterministic geometry of the sewn walks (SB, GB10, GB11, Proposition 6.12). -/
def GW4RelativeChainStatement : Prop :=
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
          ∀ᵐ ω ∂ν, ∃ (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0), Continuous Wrel ∧ Wrel 0 = 0 ∧ StrictMono T ∧
            Continuous T ∧
            (∀ t : ℝ≥0, t < T 0 → ∀ p : ℂ,
              Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) t) (𝓝[H] 0) (𝓝 p) →
              p ≠ 0 → -p⁻¹ ∉ closure C) ∧
            (∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => Wrel r.toNNReal) s =
              relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) (T s) ∩ relDom C)) ∧
            ∀ s : ℝ≥0, 0 < s →
              (∀ p : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) (T s)) (𝓝[H] 0)
                (𝓝 p) → p ≠ 0) ∧
              ∀ q : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => Wrel r.toNNReal) s) (𝓝[H] 0) (𝓝 q) →
                q ≠ 0

/-- **Named input: Theorem GW4, the identification of the relative driver** ("The full kernel and the one phase",
pp. 638–639: the marked union and optional local-set law preserve the initial GW3 kernel; at every enlarged stopping
time the full active Poisson mean and covariance; the phase `δ_s = 0` by Aux. lemma 122, which "identifies the
canonical integrated finite-word system"; universal determination). Binders and component data of
`GW4RelativeHullStatement`. Every centred counterflow `W_C` of the component field with infinite lifetime is,
`ν`-almost surely, every continuous relative driver of the ambient traversal (any continuous `W_rel` whose hulls are
`Φ(K'_{T s} ∩ R⁻¹(C))` for some continuous strictly increasing clock `T`). Since such hull families determine the
clock (nested hulls of equal capacity) and the driver (`Sec6.eqOn_of_fwdHull_eq`), this is the law statement "the
relative driver is the canonical counterflow of `h_C`". -/
def GW4RelativeIdentStatement : Prop :=
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
          ∀ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ ν hC WC ζC →
            (∀ᵐ ω ∂ν, ζC ω = ⊤) →
            ∀ᵐ ω ∂ν, ∀ (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0), Continuous Wrel → StrictMono T → Continuous T →
              (∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => Wrel r.toNNReal) s =
                relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) (T s) ∩ relDom C)) →
              (fun t => WC t ω) = Wrel

/-- **The relative-hull statement from its two halves** (conditional helper): the pathwise relative chain and the
identification of its driver. -/
theorem gw4RelativeHullStatement_of_chain_ident (hP : GW4RelativeChainStatement.{u})
    (hI : GW4RelativeIdentStatement.{u}) : GW4RelativeHullStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  filter_upwards [hP κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hPω hIω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff WC ζC hcd hζC
  filter_upwards [hPω C hCm c hC bC jumpsC hch htr hpc hbd hgff,
    hIω C hCm c hC bC jumpsC hch htr hpc hbd hgff WC ζC hcd hζC] with ω hPω' hIω'
  obtain ⟨Wrel, T, hWc, -, hT, hTc, hent, hK, hne⟩ := hPω'
  have e := hIω' Wrel T hWc hT hTc hK
  subst e
  exact ⟨T, hT, hTc, hent, hK, hne⟩

/-- **Theorem GW4's traversal core from the pathwise relative chain and the identification of its driver**
(conditional helper). -/
theorem gw4TraversalCoreStatement_of_chain_ident (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Word.BetweenComponentsOpenStatement.{u})
    (hWB : GW4.GW3WordBoundStatement.{u}) (hP : GW4RelativeChainStatement.{u})
    (hI : GW4RelativeIdentStatement.{u}) : GW4.GW4TraversalCoreStatement.{u} :=
  gw4TraversalCoreStatement_of_relHulls h12 h13 hO hWB (gw4RelativeHullStatement_of_chain_ident hP hI)

end GW4Traverse

end Theorem14

end InteractingSLE
