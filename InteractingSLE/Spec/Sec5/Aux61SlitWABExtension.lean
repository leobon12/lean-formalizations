/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWABCert
import InteractingSLE.Spec.Sec5.Aux61SlitWZInverse

/-! # Continuous inverse extension directly on certified retained records

The counterflow trace certificate and the already certified own prefix
provide the two compact traces in the existing inverse-extension theorem.
The chart is the literal chart of `RestartChoices`, with no normalization
or continuation hypothesis.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open QuantumZipper.CA (cayley)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAB
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61Restart Aux61FibData Aux61GInst Aux61ULoc LawUnique
open WangWu (negInv)
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- Both canonical inverse-extension clauses on an initial record.
The record's own regularity and counterflow trace certificates supply
all analytic hypotheses, independently of chart normalization. -/
theorem record_extension (i : C.Idx) {y : SourceRecord S.nL S.nR}
    (hy : y ∈ C.toR1Restart.selected i)
    (hcf : y.1 ∈ counterflowCertified (rationalTime S.s)) :
    EqOn (boundedInverse (C.toR1Restart.chart C.hasChart i y))
        (cayley ∘ (C.toR1Restart.chart C.hasChart i y).2.1) H ∧
      ContinuousOn (boundedInverse (C.toR1Restart.chart C.hasChart i y)) Hbar := by
  have hgood : y ∈ goodSet (rationalTime S.s) (C.q i.1) := hy.2
  obtain ⟨hq, -, -, -, -, hH, hηc, hη0, -⟩ := hgood.1.facts
  obtain ⟨b, hdom⟩ := (C.toR1Restart.chart_spec C.hasChart i).2.2.1
  have hdomy := hdom y
  change ((C.toR1Restart.chart C.hasChart i y).dom : Set ℂ) =
    restartComponent (historyHull (rationalTime S.s) (finY (rationalTime S.s) (C.q i.1)) y)
      (finη (rationalTime S.s) (C.q i.1) y) (C.q i.1) (b y) at hdomy
  rw [historyHull, finY_of_mem hgood, finη_of_mem hgood, cfDrv0_eq_frozenDrv hcf.1] at hdomy
  have hc := (C.toR1Restart.chart_spec C.hasChart i).2.1 y
  have hb : b y ∈ retainedDomain
      (negInv '' fwdHull (Ito.rpath (frozenDrv (rationalTime S.s) y.1)) (rationalTime S.s))
      (recη (C.q i.1) y) (C.q i.1) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ _).Nonempty
    rw [← hdomy]
    exact ⟨_, hc.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hηH : MapsTo (recη (C.q i.1) y) (Icc 0 (C.q i.1 : ℝ)) Hbar := by
    intro t ht
    rcases ht.1.eq_or_lt with ht0 | ht0
    · rw [← ht0, hη0]
      exact zero_mem_Hbar
    · exact QuantumZipper.H_subset_Hbar (hH ⟨ht0, ht.2⟩)
  have hF := boundedInverse_spec_of_traces
    (hcf.1.isLoewnerTrace_fullTrace hcf.2 (rationalTime_s_pos S))
    (rationalTime S.s).coe_nonneg hηc hηH hb hc hdomy
  exact ⟨hF.1, hF.2.1⟩

end InteractingSLE.Sec5.Aux61SlitWAB
