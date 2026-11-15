/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRNextAssemble
import InteractingSLE.Spec.Supplement.GW4SafeRNextWord

/-!
# GW4: the remaining conditional component input, with all wiring proved

`GW4ComponentLinesStatement` is an unproved mathematical input, explicitly named
at the orchestrator's request. It asserts only the marked local-set law in the
selected conditional component and the actual finite-word mean there. The
conclusions of `gw4RelSafeRStatement_of_componentLines` and
`gw4RelativeLawRegStatement_of_componentLines` remain conditional on that input.
No frozen declaration is changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.StripSysField GW4Rel GW4Traverse Exist.StagedLaw Supp8.Q3Stop Supp8.GB6.RelDrv Restart

/-- **Unproved mathematical input, conditional component line form of Q3.**
In the actual GW4 conditioning, every good frame and path-rule version has the
marked component locality and finite-word mean specified by `HasComponentLines`.
The global original-space kernel is proved in `GW4SafeRKernel`; the component
restriction/disintegration and incident-side mean/phase calculation are the
remaining mathematics represented by this hypothesis. -/
def GW4ComponentLinesStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔
            pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L,
        ∀ (c : Chart) (hC : Ω → DistOn upperHalfPlaneOpens)
          (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b
            (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
        ∀ c₀ : BoundaryWord, c₀.IsSorted → c₀.jumps = counterflowJumps jumpsC →
          (∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) →
        ∀ (F : Frame) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω),
          F.IsOk → F.C = C → F.c = c →
          (∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) →
        ∀ hWm : ∀ r, Measurable (Wd r), MeasurableSet GT → (∀ᵐ ω ∂ν, ω ∈ GT) →
          (∀ᵐ ω ∂ν, ∀ t, Wd t ω = W' t ω) →
        ∀ (Rv : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞),
          IsGW4RelVersionR ν Wd F.c F.C Rv V →
          HasComponentLines (16 / κ) c₀ F ν (fun ω => invField κ (hC ω)) Wd GT Rv V hWm

/-- The requested path-rule safe law from the explicitly named conditional
component line input. The word bounds are instantiated with a canonical driver,
so no law of the physical relative driver is presumed in this argument. -/
theorem gw4RelSafeRStatement_of_componentLines
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hLines : GW4ComponentLinesStatement.{u}) : GW4RelSafeRStatement.{u} := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [exists_frame h13 hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hWB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hLines κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hFr hBound hLine
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ Rv V hver
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  let X := fun ω => invField κ (hC ω)
  have hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps :=
    isGFFWithBoundaryData_invField_word hκ hpc hgff hc₀J hc₀
  have hk : 0 < 16 / κ := by positivity
  have hcan := isFlowLineDriver_cfDrv_word h12p h13 hk c₀ hX
  obtain ⟨hsL, hsR⟩ := hBound C hCm c hC bC jumpsC hch htr hpc hbd hgff
    c₀.fn c₀.jumps X (fun t ω => (BRLeaf.cfDrv h12p hk c₀ (X ω)).1 t)
    (fun ω => (BRLeaf.cfDrv h12p hk c₀ (X ω)).2) c₀.isPiecewiseConstantBoundaryData
    (fun ω => isChartTransport_invField hκ (hC ω)) hcan
  obtain ⟨F, Wd, GT, hF, hFC, hFc, hGT, hWm, hGTm, hGTae, hVW⟩ := hFr C hCm c hch
  have hvd : IsGW4RelVersionR ν Wd F.c F.C Rv V := by
    rw [hFC, hFc]
    exact hver.of_ae_eq hVW
  have hlocal := hLine C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hvd
  exact hasRelSafe_of_componentLines hX hF hGT hWm hGTm hGTae hvd hsL hsR hlocal

/-- The component relative law needed by the Theorem 1.4 relay, now conditional
on the local-set and mean input rather than on a relative stochastic law. -/
theorem gw4RelativeLawRegStatement_of_componentLines
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hLines : GW4ComponentLinesStatement.{u}) : GW4Reg.GW4RelativeLawRegStatement.{u} :=
  gw4RelativeLawRegStatement_of_relSafeR h12 h13 h12₀ h13₀ hB hWB
    (gw4RelSafeRStatement_of_componentLines h12 h13 hB hWB hLines)

end InteractingSLE.Theorem14.GW4Fix
