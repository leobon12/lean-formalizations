/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11
import InteractingSLE.Spec.Supplement.GW4IdentLaw

/-!
# Theorem GW4: the pathwise relative chain from GB10, GB11 and the sewn barrier

Packet PROVE-T14-GW4R. `GW4Traverse.GW4RelativeChainStatement` (PROVE-T14-GW4T; Theorem GW4's proof, "The
between-region and the actual intervals", pp. 637–638) asks, `ν`-almost surely and for every between-component `C`
with a component chart `c`, for a continuous relative driver from `0` and a continuous strictly increasing clock with
the entry clause, the relative hulls `Φ(K'_{T s} ∩ R⁻¹(C))` and nonvanishing tips. Here it is proved from

* **`GB10.GB10Statement`** (Lemma GB10, p. 555), applied to the ambient counterflow (an integrated `SLE_{16/κ}(ρ)`
  evolution, `16/κ > 4`) under `P` and moved to `ν`;
* **`GB11.GB11Statement`** (Lemma GB11, pp. 556–557, deterministic form);
* **`GW4BarrierStatement`** (named input; GW4's proof p. 637: "The sewn-barrier conclusion and GW2 first put the
  entire counterflow range on the closed left of `R` and the closed right of `L`. GW1 puts both walks in that same
  range. … Every common contact is ordered the same way on the two walks … An interior common open subarc is
  impossible … A common original-real interval is also impossible"; GW1: the walks are field-determined continuous
  injective proper curves): `ν`-almost surely the walks are complete simple flows with GB11's barrier input;
* **`GW4CompletionStatement`** (named input; GW4's proof p. 639: "The relative endpoint is the designated `x_C`, hence
  is infinity in the reversed chart. All cumulative groups are greater than `−2` by GW3. At a proposed finite relative
  lifetime, integrated nonexplosion and bounded-coordinate localization would bound the whole relative hull,
  contradicting that endpoint. The relative lifetime is infinite"): every maximal relative parametrization of a
  traversal has infinite relative capacity, and at positive relative times neither tip is at its chart's infinity;
* Theorem 1.3 (the ambient trace).

Assembly with the identification (`GW4IdentLaw.lean`): `gw4RelativeHullStatement_of_inputs`,
`gw4TraversalCoreStatement_of_inputs`, and `componentKernels_of_inputs` (the frozen component-kernel anchor's
conclusion, binders verbatim, from the finest inputs).

**R43/R48.** Theorems 1.2–1.3 are used; GW4 serves Theorem 1.4 only.
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

namespace GW4Ident

open GW4Traverse

/-! ### The two remaining named inputs of the chain -/

/-- **Named input: the barrier input of GB11 for the actual sewn walks** (Theorem GW4's proof, p. 637, "The
between-region and the actual intervals"; SB, GW1, GW2). Binders of `GW4Traverse.GW4RelativeChainStatement` up to the
walks (verbatim). Almost surely the two walks are the ranges of complete simple flows `α_R`, `α_L` from `0` to `∞` (GW1:
"a field-determined continuous injective proper curve"), and `ν`-almost surely they satisfy GB11's barrier input with
every generating trace of the ambient counterflow (same contact order, no common open subarc, the closed
between-region containing the counterflow, both walks visited in strict reverse first-visit order). -/
def GW4BarrierStatement : Prop :=
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
        ∃ αR αL : ℝ≥0 → ℂ, range αR = R ∧ range αL = L ∧
          ∀ᵐ ω ∂ν, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → GB11.IsGB11Barrier αR αL γ

/-- **Named input: the completion of each traversal** (Theorem GW4's proof, p. 639: "The relative endpoint is the
designated `x_C`, hence is infinity in the reversed chart. All cumulative groups are greater than `−2` by GW3. At a
proposed finite relative lifetime, integrated nonexplosion and bounded-coordinate localization would bound the whole
relative hull, contradicting that endpoint. The relative lifetime is infinite"). Binders and component data of
`GW4Traverse.GW4RelativeChainStatement` (verbatim). `ν`-almost surely, for every generating trace of the ambient
counterflow, every maximal relative parametrization of the traversal of `C` (`GB11.IsGB11RelParam`) has infinite
relative capacity `S = ∞`, and at positive relative times neither tip is at its chart's infinity (the traversal does
not return to its entry `y_C` nor to the original source). -/
def GW4CompletionStatement : Prop :=
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
          ∀ᵐ ω ∂ν, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ →
            ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) →
            ∀ (S : ℝ≥0∞) (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0),
              GB11.IsGB11RelParam (fun t => W' t ω) γ c C xC S Wrel T →
              S = ⊤ ∧ ∀ s : ℝ≥0, 0 < s →
                (∀ p : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) (T s)) (𝓝[H] 0)
                  (𝓝 p) → p ≠ 0) ∧
                ∀ q : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => Wrel r.toNNReal) s) (𝓝[H] 0) (𝓝 q) →
                  q ≠ 0

/-! ### The chain -/

/-- `16/κ > 4` for `0 < κ < 4`. -/
theorem four_lt_sixteen_div {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : 4 < 16 / κ := by
  rw [lt_div_iff₀ hκ]
  linarith

/-- The punctured approach to `0` within `ℍ` is a nontrivial filter. -/
theorem neBot_nhdsWithin_H_zero : (𝓝[H] (0 : ℂ)).NeBot := tendsto_radial.neBot

/-- **GB10 for the ambient counterflow, with its trace** (`P`-almost surely): the centred counterflow is an integrated
`SLE_{16/κ}(ρ)` evolution (`16/κ > 4`) with infinite lifetime and a continuous generating trace (Theorem 1.3), which
has no time interval in a compact simple arc (GB10). -/
theorem ae_trace_noSimpleArcInterval (hGB10 : GB10.GB10Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    ∀ᵐ ω ∂P, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧ ∃ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W' t ω) ⊤ γ ∧ GB10.NoSimpleArcInterval γ ⊤ := by
  obtain ⟨b', J', h', -, -, hfl⟩ := id hcf
  obtain ⟨h'', 𝓕, VL, VR, B, -, hcoup⟩ := hfl
  have hG := hGB10 (16 / κ) (four_lt_sixteen_div hκ hκ4) _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b' J' 0)
    P 𝓕 W' VL VR B ζ' hcoup.1
  filter_upwards [hG, ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ', hζ'] with ω hGω htrω hζω
  obtain ⟨hc, h0, γ, hγ, -⟩ := htrω
  rw [hζω] at hGω
  exact ⟨hc, h0, γ, hγ, hGω γ hγ⟩

/-- **Theorem GW4's pathwise relative chain** (conditional helper with a distinct name) from Lemma GB10, Lemma GB11,
the barrier input of the actual walks, the completion of each traversal, and Theorem 1.3. -/
theorem gw4RelativeChainStatement_of_gb11 (h13 : Exist.Theorem13Statement.{u}) (hGB10 : GB10.GB10Statement.{u})
    (hGB11 : GB11.GB11Statement) (hB : GW4BarrierStatement.{u}) (hComp : GW4CompletionStatement.{u}) :
    GW4RelativeChainStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_noSimpleArcInterval hGB10 h13 hκ hκ4 hcf hζ')
  filter_upwards [hamb, hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    hComp κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hambω hBω hCω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  obtain ⟨αR, αL, hαR, hαL, hbar⟩ := hBω
  filter_upwards [hambω, hbar, hCω C hCm c hC bC jumpsC hch htr hpc hbd hgff] with ω hambω' hbarω hcompω
  obtain ⟨hW'c, hW'0, γ, hγ, hno⟩ := hambω'
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  obtain ⟨xC, hxC, -, -⟩ := hch.2.2.2.2.1 0
  have hxC' : Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) := by simpa only [Complex.ofReal_zero] using hxC
  obtain ⟨S, Wrel, T, hpar, hent, -, -⟩ := hGB11 (fun t => W' t ω) γ hW'c hW'0 hγ hno αR αL (hbarω γ hγ) C hCm'
    c hch' xC hxC'
  obtain ⟨hS, htips⟩ := hcompω γ hγ xC hxC' S Wrel T hpar
  subst hS
  obtain ⟨hWc, hW0, hTm, hTc, hK⟩ := hpar.global
  have := neBot_nhdsWithin_H_zero
  refine ⟨Wrel, T, hWc, hW0, hTm, hTc, fun t ht p hp hp0 => ?_, hK, htips⟩
  have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hW'c.continuousOn hW'0
    (ENNReal.coe_lt_top (r := t))
  have e : p = γ t := tendsto_nhds_unique hp htip
  subst e
  exact hent t ht hp0

/-! ### Assembly -/

/-- **Theorem GW4's relative-hull statement from the finest inputs** (conditional helper): GB10, GB11, the barrier
input of the actual walks, the completion of each traversal, the component (Det), Theorems 1.2–1.3. -/
theorem gw4RelativeHullStatement_of_inputs (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hGB10 : GB10.GB10Statement.{u}) (hGB11 : GB11.GB11Statement) (hB : GW4BarrierStatement.{u})
    (hComp : GW4CompletionStatement.{u}) (hL : GW4RelativeLawStatement.{u}) : GW4RelativeHullStatement.{u} :=
  gw4RelativeHullStatement_of_chain_law h12 h13 (gw4RelativeChainStatement_of_gb11 h13 hGB10 hGB11 hB hComp) hL

/-- **Theorem GW4's traversal core from the finest inputs** (conditional helper). -/
theorem gw4TraversalCoreStatement_of_inputs (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Word.BetweenComponentsOpenStatement.{u})
    (hWB : GW4.GW3WordBoundStatement.{u}) (hGB10 : GB10.GB10Statement.{u}) (hGB11 : GB11.GB11Statement)
    (hB : GW4BarrierStatement.{u}) (hComp : GW4CompletionStatement.{u}) (hL : GW4RelativeLawStatement.{u}) :
    GW4.GW4TraversalCoreStatement.{u} :=
  gw4TraversalCoreStatement_of_relHulls h12 h13 hO hWB
    (gw4RelativeHullStatement_of_inputs h12 h13 hGB10 hGB11 hB hComp hL)

/-- **Theorem 1.4, component kernels** (Specification p. 5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, from the finest named inputs after this packet: Lemma GW3's
between-region geometry and one-chart field law, the walks' no-common-continuum and connector-side facts, GW0's forward
implication, Lemmas GB10 and GB11, the barrier input of the actual walks, the completion of each traversal, the
component (Det), and Theorems 1.2–1.3 (the types of the frozen anchors). -/
theorem componentKernels_of_inputs (hG : GW3.GW3GeometryStatement.{u})
    (hF1 : GW3Law.GW3FieldLawOneChartStatement.{u}) (hN : GW3Law.WalkNoCommonContinuumStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hS : GW3Word.WalkConnectorSideStatement.{u})
    (hGB10 : GB10.GB10Statement.{u}) (hGB11 : GB11.GB11Statement) (hB : GW4BarrierStatement.{u})
    (hComp : GW4CompletionStatement.{u}) (hL : GW4RelativeLawStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
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
  componentKernels_of_relHulls hG hF1 hN hGW0 hS
    (gw4RelativeHullStatement_of_inputs h12 h13 hGB10 hGB11 hB hComp hL) h12 h13 hκ hκ4 b jumps hb hh hcf hζ' E hE

end GW4Ident

end Theorem14

end InteractingSLE
