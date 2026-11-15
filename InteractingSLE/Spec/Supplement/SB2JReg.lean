/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JUpper
import InteractingSLE.Spec.Supplement.GW1ExtWire

/-!
# SB2(1)'s remaining named input (rulings R96, R94) for families regular at every sample

Packet PROVE-T14-SB2FIN4. Ruling R96 restores the counterflow binder in SB2(1): the named input is
`GW1Ext.SB2RelDriverCfStatement`, whose clause (0) (`m ≤ 0`) PROVE-GW1-EXTREC proved in the counterflow setting
(`GW1Ext.ae_launchEntry_nonpos_of_counterflow`), so clauses (1)–(3) remain. Every route to K2's inputs for them
(`SB.Cond.isCondFlowLineDriverOn_of_markedKernel`) needs drivers regular at EVERY sample: the version chart measurable
in the retained past (`WalkInf.verChart`, `isMeasChart_verChart`), the kernel-almost sure constancy of the run chart
(`Cond.ae_ae_runChart_eq`) and the past-measurable conditional word (`Cond.exists_condChartField_of_isStagedHistory`)
all assume `∀ j ω, IsRegularDriver (E j ω)`. This file

* states the remaining input with the counterflow binder, `SB2RelCoreCfStatement` (`GW1Ext.SB2RelDriverCoreStatement`
  plus the binder — weaker, so `relCoreCf_of_core`), and wires it: **`sb2RelDriverCfStatement_of_relCoreCf`** (clause
  (0) from `GW1Ext.ae_launchEntry_nonpos_of_counterflow`, Theorem 1.3 at universe `0`);
* removes the regularity hypothesis once and for all: `SB2RelCoreCfRegStatement` (families regular at every sample)
  and **`sb2RelCoreCfStatement_of_reg`** (Theorem 1.3), through the regularized family `StagedReg.regFam E` (a staged
  history, regular at every sample, `StagedPiecesRegular` by `Exist.StagedLaw.stagedPiecesRegular_of_regular`, with
  almost surely the same runs): launch event, launch chart, entry point and retained prefix agree almost surely
  (`launch_objects_eq_of_run_eq`); the regular conditional laws given the two retained pasts agree almost surely
  (`StagedReg.ae_condExpKernel_eq_of_ae_eq` with `StagedReg.ae_pastMap_regHist`); the pathwise link passes under almost
  every conditional law (`Sec7.Aux122Disint.ae_ae_condExpKernel`).

R48: Theorem 1.3 is a hypothesis; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged

/-- **Named input: SB2(1)'s clauses (1)–(3) in the counterflow setting** (ruling R96): `GW1Ext.SB2RelDriverCfStatement`
without its clause (0) — K2's conditional flow-line driver in the launch chart recentred at its entry, SB2(1)'s
active word for every witness, and the pathwise link — for a field with a complete centred counterflow. -/
def SB2RelCoreCfStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) P (launchSet κ b jumps E k) h
        (fun ω => (launchChart κ b jumps E k ω).recenter (launchEntry κ b jumps E k u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E k ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E k u ω₀)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
          IsRemainderLink (launchChart κ b jumps E k ω₀) (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E k u ω₀) (ζr ω))

/-- **`SB2RelCoreCfStatement` for families regular at every sample** (the extra hypothesis
`∀ spec j ω, IsRegularDriver (E spec j ω)` after `StagedPiecesRegular`). -/
def SB2RelCoreCfRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (j : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec j ω)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) P (launchSet κ b jumps E k) h
        (fun ω => (launchChart κ b jumps E k ω).recenter (launchEntry κ b jumps E k u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E k ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E k u ω₀)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
          IsRemainderLink (launchChart κ b jumps E k ω₀) (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E k u ω₀) (ζr ω))

/-- **The run-determined objects of the lower walk agree where the runs agree**: the launch event, the launch chart,
the retained prefix, the entry point and `Lx.LowerLaunch` at stage `k`. -/
theorem launch_objects_eq_of_run_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E E' : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}
    (hω : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E' (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n) (k : ℕ) (u : ℝ) :
    (ω ∈ launchSet κ b jumps E' k ↔ ω ∈ launchSet κ b jumps E k) ∧
      launchChart κ b jumps E' k ω = launchChart κ b jumps E k ω ∧
      lowerPrefix κ b jumps E' k u ω = lowerPrefix κ b jumps E k u ω ∧
      launchEntry κ b jumps E' k u ω = launchEntry κ b jumps E k u ω ∧
      (Lx.LowerLaunch κ b jumps E' k ω ↔ Lx.LowerLaunch κ b jumps E k ω) := by
  have hP : lowerPrefix κ b jumps E' k u ω = lowerPrefix κ b jumps E k u ω := by
    simp only [lowerPrefix, prefixPhysSet, hω]
  have hC : launchChart κ b jumps E' k ω = launchChart κ b jumps E k ω := by
    simp only [launchChart, hω]
  refine ⟨by simp only [launchSet, mem_ofPred_eq, hω], hC, hP, ?_, by simp only [Lx.LowerLaunch, lowerWalkState, hω]⟩
  simp only [launchEntry, hP, hC]


/-- PROVE-GW1-EXTREC's `SB2RelDriverCoreStatement` (no counterflow binder) implies the counterflow form. -/
theorem relCoreCf_of_core (hC : GW1Ext.SB2RelDriverCoreStatement.{u}) : SB2RelCoreCfStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh _ _ _ _ E hE hER k u ψ hu hψ hL hH η ζ hη hone
  exact hC κ hκ hκ4 b jumps hb P h hh E hE hER k u ψ hu hψ hL hH η ζ hη hone

/-- **SB2(1)'s named input in the counterflow setting from clauses (1)–(3)** (ruling R96): clause (0) is
`GW1Ext.ae_launchEntry_nonpos_of_counterflow` (Theorem 1.3 at universe `0`). -/
theorem sb2RelDriverCfStatement_of_relCoreCf (hT13₀ : Exist.Theorem13Statement.{0})
    (hC : SB2RelCoreCfStatement.{u}) : GW1Ext.SB2RelDriverCfStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER k u ψ hu hψ hL hH η ζ hη hone
  obtain ⟨bc, jc, W, ζr, hK, hword, hlink⟩ :=
    hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER k u ψ hu hψ hL hH η ζ hη hone
  exact ⟨bc, jc, W, ζr, GW1Ext.ae_launchEntry_nonpos_of_counterflow hT13₀ hκ hκ4 hb hh hcf hζ' hE hER k hu, hK,
    hword, hlink⟩

/-- **SB2(1)'s remaining input for general families from the form for families regular at every sample** (the
regularized family `StagedReg.regFam E`; Theorem 1.3 gives its `StagedPiecesRegular`). -/
theorem sb2RelCoreCfStatement_of_reg (h13 : Exist.Theorem13Statement.{u})
    (hrel : SB2RelCoreCfRegStatement.{u}) : SB2RelCoreCfStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER k u ψ hu hψ hL hH η ζ hη hS1
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    Exist.StagedLaw.stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hrw := hrun _ hw
  -- the regular conditional laws given the two retained pasts agree almost surely
  have hpm' : Measurable (pastMap κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) :=
    Measurable.of_comap_le ((hE' _ hw).2.1 k)
  have hpm : Measurable (pastMap κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) :=
    Measurable.of_comap_le ((hE _ hw).2.1 k)
  have hK : ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀ =
      condExpKernel P (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀ :=
    StagedReg.ae_condExpKernel_eq_of_ae_eq hpm' hpm (StagedReg.ae_pastMap_regHist (hER _ hw) k)
  have hS1' : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (lowerPrefix κ b jumps (StagedReg.regFam E) k u ω) (η ω) a := by
    filter_upwards [hS1, hrw] with ω hω hr a ha
    rw [(launch_objects_eq_of_run_eq hr k u).2.2.1]
    exact hω a ha
  obtain ⟨bc, jc, W, ζr, h1, h2, h3⟩ :=
    hrel κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hR' hreg' k u ψ hu hψ hL hH η ζ hη hS1'
  refine ⟨bc, jc, W, ζr, ?_, ?_, ?_⟩
  · filter_upwards [h1, hrw, hK] with ω₀ hω₀ hr hk hF
    have e := launch_objects_eq_of_run_eq hr k u
    rw [← e.2.1, ← e.2.2.2.1, ← hk]
    exact hω₀ (e.1.2 hF)
  · filter_upwards [h2, hrw, hK] with ω₀ hω₀ hr hk hF b' J' h' hb' hT' hG'
    have e := launch_objects_eq_of_run_eq hr k u
    rw [← e.2.1] at hT'
    rw [← hk] at hG'
    rw [← e.2.2.2.1]
    exact hω₀ (e.1.2 hF) b' J' h' hb' hT' hG'
  · filter_upwards [h3, hrw, hK, Sec7.Aux122Disint.ae_ae_condExpKernel ((hE _ hw).2.1 k) hrw]
      with ω₀ hω₀ hr hk hrr hF
    have e := launch_objects_eq_of_run_eq hr k u
    rw [← hk]
    filter_upwards [hω₀ (e.1.2 hF), (show ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
        (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀), _ from hk ▸ hrr)]
      with ω hω hrω
    have e' := launch_objects_eq_of_run_eq hrω k u
    rw [← e.2.1, ← e.2.2.2.1, ← e'.2.2.1]
    exact hω

end InteractingSLE.Theorem14.SB.Lv
