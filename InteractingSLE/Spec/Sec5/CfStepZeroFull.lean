/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfStep44Facts

/-!
# Complete zero-prefix data under the two (4.4) height bounds

Packet PROVE-CFCHART2. This is the exact zero-time branch, including physical
members and the physical clock, from the two (4.4) bounds and flow hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfStep

open CfConv CfGiven Exist Exist.Staged Exist.StagedLaw Restart Restart.DomainMarkov.K2
open Sec7.PocketTraversal
open Sec7.StripHeights44 (IsHeightBounded44)

/-- Every clause of the fixed-time counterflow chart statement at prefix time zero.
The retained trace is the supplied trace; its physical clock is the identity. -/
theorem exists_zero_chartConst_omega44 {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hθh : IsHeightBounded44 κ b J θ) (hπh : IsHeightBounded44 κ b J (π / 2))
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D)
    (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    {η₀ : Ω → ℝ≥0 → ℂ}
    (hη₀ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η₀ ω)) :
    ∃ (𝓐 : Filtration ℝ≥0 mΩ) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
      (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
      (V : ℝ≥0 → Ω → ℝ) (η : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap (fun ω => recOf 0 (D ω)) inferInstance ≤ 𝓐 0 ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf 0 (D ω)) inferInstance] xL ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf 0 (D ω)) inferInstance] xR ∧
      (∀ ω i, xL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ xR ω j) ∧
      (∀ ω, Antitone (xL ω)) ∧ (∀ ω, Monotone (xR ω)) ∧
      (∀ ω, V 0 ω = 0) ∧ (∀ ω, Continuous fun t => V t ω) ∧ StronglyAdapted 𝓐 V ∧
      (∀ᵐ ω ∂P, FCDet.thr ρL ρR V xL xR ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => imgField κ (recOf 0 (D ω)) (h ω) φ) P) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 V (geomLW V xL) (geomRW V xR)
        (fun _ => ⊤) (fun ω => cfChart (recOf 0 (D ω))) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      HasSafeMembers P 𝓐 univ (fun _ => ⊤) V (fun ω => imgField κ (recOf 0 (D ω)) (h ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => V t ω) ⊤ (η ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → WangWu.negInv (η ω u) ∈ H ∧
            WangWu.negInv (η₀ ω (ℓ u)) =
              (recChart (recOf 0 (D ω))).2.1 (WangWu.negInv (η ω u)) := by
  obtain ⟨hDtop, hH⟩ := ae_top_and_interior_of44
    hA href hκ hκ4 hb hcf hζ' hθh hπh hθ hD hη₀
  have hDpos : ∀ᵐ ω ∂P, 0 < (D ω).2 := hDtop.mono fun _ hω => hω ▸ ENNReal.zero_lt_top
  obtain ⟨c, 𝓐, V, h𝒢, hV0, hVc, hVa, he, hthr, hchart, hmem⟩ :=
    exists_zero_regular_chart_members hκ hcf hζ' hDm hDreg hDpos
  have hord := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  refine ⟨𝓐, flowLineNL c.fn c.jumps 0, flowLineNR c.fn c.jumps 0,
    flowLineRhoL (16 / κ) c.fn c.jumps 0 0, flowLineRhoR (16 / κ) c.fn c.jumps 0 0,
    (fun _ => flowLineXL c.fn c.jumps 0), (fun _ => flowLineXR c.fn c.jumps 0), V, η₀,
    h𝒢, measurable_const, measurable_const, (fun _ => hord.2.1), (fun _ => hord.2.2.2),
    (fun _ => hord.1), (fun _ => hord.2.2.1), hV0, hVc, hVa, hthr, ?_,
    CfResume.integrable_imgField_recOf_zero hcf D, hchart, hmem, ?_⟩
  · exact ae_of_all _ fun _ => ⟨c, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · filter_upwards [he, hη₀, CfResume.ae_physical_clock_zero D hH] with ω hω htr hclock
    refine ⟨?_, hclock⟩
    have hVW : (fun t => V t ω) = fun t => W' t ω := funext hω
    rwa [hVW]

/-- The exact (4.4) zero-prefix leaf, with no additional chart or locality premise. -/
theorem zeroChart44Statement (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : QSched.ZeroChart44Statement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ θ hθ hθh hπh D hDm hDreg hD η hη
  exact exists_zero_chartConst_omega44 hA href hκ hκ4 hb hcf hζ hθh hπh hθ hDm hDreg hD hη

end InteractingSLE.Sec5.CfStep
