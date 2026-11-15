/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11Proof
import InteractingSLE.Spec.Supplement.GW4R51

/-!
# Theorem GW4's traversal core and the version-2 component kernels from the R51 relative chain

Packet PROVE-T14-GW4T2. Joins the R51 relative chain (`GW4LawProofReg.lean`) to PROVE-T14-GW8's R51 assembly
(`GW4R51.lean`):

* `gw4TraversalCoreRegStatement_of_relHulls`: `GW4R51.GW4TraversalCoreRegStatement` from the R51 relative hulls, the
  openness of the between-components and GW3's word bounds (`GW4Traverse.gw4TraversalCoreStatement_of_relHulls` with
  `hreg` threaded through);
* `gw4TraversalCoreRegStatement_of_law`: the same from GB11, the R51 barrier and law inputs, the deterministic filled
  pocket, no return and Theorems 1.2–1.3;
* `gw4TraversalCoreRegStatement_of_barrierShape`: the same with the barrier input carrying the walks' exit shape
  (`GW4FillDetProof.lean`), so that the deterministic fill input is not needed;
* `gw4TraversalCoreRegStatement_of_relParam`: the same with Lemma GB11 reduced to its relative parametrization and the
  barrier input carrying the walks' pocket shape (`GB11Proof.lean`);
* **`componentKernels_of_lawReg`**: the version-2 (R51) component-kernel anchor's type, provider shape, from
  PROVE-T14-GW8's finest inputs (`GW4R51.componentKernels_of_unionLaw`) with the traversal core replaced by the inputs
  of the relative chain: the relative parametrization of a pocket traversal (`GB11RelParamStatement`), the barrier
  input with the pocket shape, the R51 component law input and no return.

Every theorem is a conditional helper with a distinct name; none is a provider.
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

namespace GW4Reg

open GW4Traverse GW4Ident

/-- **Theorem GW4's traversal core from the relative hulls, R51 form**
(`GW4Traverse.gw4TraversalCoreStatement_of_relHulls` with `hreg` threaded through). -/
theorem gw4TraversalCoreRegStatement_of_relHulls (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Joint.BetweenComponentsOpenRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hH : GW4RelativeHullRegStatement.{u}) :
    GW4R51.GW4TraversalCoreRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hO' := hO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
  have hW' := hWB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
  have hH' := hH κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg
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

/-- **Theorem GW4's traversal core, R51 form, from the inputs of the relative chain** (conditional helper). -/
theorem gw4TraversalCoreRegStatement_of_law (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Joint.BetweenComponentsOpenRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hGB11 : GB11.GB11Statement) (hB : GW4BarrierRegStatement.{u})
    (hL : GW4RelativeLawRegStatement.{u}) (hD : GW4FillDetStatement) (hNR : CounterflowNoReturnStatement.{u}) :
    GW4R51.GW4TraversalCoreRegStatement.{u} :=
  gw4TraversalCoreRegStatement_of_relHulls h12 h13 hO hWB
    (gw4RelativeHullRegStatement_of_law h12 h13 hGB11 hB hL hD hNR)

/-- **Theorem GW4's traversal core, R51 form, from the barrier input with the exit shape** (conditional helper; no
deterministic fill input). -/
theorem gw4TraversalCoreRegStatement_of_barrierShape (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Joint.BetweenComponentsOpenRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hGB11 : GB11.GB11Statement)
    (hB : GW4BarrierShapeRegStatement.{u}) (hL : GW4RelativeLawRegStatement.{u})
    (hNR : CounterflowNoReturnStatement.{u}) : GW4R51.GW4TraversalCoreRegStatement.{u} :=
  gw4TraversalCoreRegStatement_of_relHulls h12 h13 hO hWB
    (gw4RelativeHullRegStatement_of_barrierShape h12 h13 hGB11 hB hL hNR)

/-- **Theorem GW4's traversal core, R51 form, from the relative parametrization input** (conditional helper; GB10, the
remaining clauses of GB11 and the filled pocket are proved). -/
theorem gw4TraversalCoreRegStatement_of_relParam (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Joint.BetweenComponentsOpenRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hR : GB11RelParamStatement)
    (hB : GW4BarrierPocketRegStatement.{u}) (hL : GW4RelativeLawRegStatement.{u})
    (hNR : CounterflowNoReturnStatement.{u}) : GW4R51.GW4TraversalCoreRegStatement.{u} :=
  gw4TraversalCoreRegStatement_of_relHulls h12 h13 hO hWB
    (gw4RelativeHullRegStatement_of_relParam h12 h13 hR hB hL hNR)

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape, from PROVE-T14-GW8's finest inputs
(`GW4R51.componentKernels_of_unionLaw`: GW3's sided geometry, the marked union law, the right walk proper, the sides of
the real connectors, the piece statement) with GW4's traversal core replaced by the inputs of the relative chain:
the relative parametrization of a pocket traversal, the barrier input with the walks' pocket shape, the R51
component-law input and no return; and Theorems 1.2–1.3 (conditional helper; not the provider). -/
theorem componentKernels_of_lawReg (hGS : GW3Sided.GW3GeometrySidedRegStatement.{u})
    (hU : GW3Joint.GW3UnionLawRegStatement.{u}) (hP : WalkCont.RightWalkProperRegStatement.{u})
    (hS : WalkCont.WalkConnectorSideRegStatement.{u}) (hNP : WalkCont.WalkPieceContinuumRegStatement.{u})
    (hR : GB11RelParamStatement) (hB : GW4BarrierPocketRegStatement.{u}) (hL : GW4RelativeLawRegStatement.{u})
    (hNR : CounterflowNoReturnStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
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
  have hO := GW3Sided.betweenComponentsOpenRegStatement_of_geometry (GW3Sided.gw3GeometryRegStatement_of_sided hGS)
  GW4R51.componentKernels_of_unionLaw hGS hU hP hS hNP
    (gw4TraversalCoreRegStatement_of_relParam h12 h13 hO
      (GW4R51.gw3WordBoundRegStatement_of_inputs hO (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS)
      hR hB hL hNR) h12 h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hreg

end GW4Reg

end Theorem14

end InteractingSLE
