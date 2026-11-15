/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbStmt
import InteractingSLE.Spec.Supplement.GW2ScheduleIdent
import InteractingSLE.Spec.Sec7.Aux122Disint
import InteractingSLE.Spec.Sec5.CfRegQ

/-!
# The stage field law in the relative chart, in law-transfer form (D76, RELDET's piece for STAGEMEAN)

Packet PROVE-GW2-STAGEMEAN, R125 round (D76 item 3: STAGEMEAN helps RELDET with the stage law as a flow-line statement
in a chart; the piece RELDET named under "For STAGEMEAN"). RELDET's `GW2Rd.StageFieldLawXStatement` (`GW2UbStmt`):
an event of `(word, field)` that is null for every GFF with the data of a sorted word is null for `(β (srecX), Hr)` on
the stage's record event. From `OpenLinesX.condGFF`:

* under the conditional kernel `ν ω₀` (σ-algebra `𝒢` of `condGFF`) the record is almost surely `srecX ω₀` (it is
  `𝒢`-measurable with values in the second countable `RecData`; `Sec7.Aux122Disint.ae_ae_condExpKernel_eq`);
* so `ν ω₀ {(β (srecX), Hr) ∈ A} = (ν ω₀).map Hr {g | (β (srecX ω₀), g) ∈ A}`, and `(ν ω₀).map Hr` is a GFF law
  with the word's data (`Sec5.CfRegQ.isGFFWithBoundaryData_of_map_eq`): the event is `ν ω₀`-null;
* the `𝒢`-measurable event `{ν · {…} = 0}` then carries the conclusion to `P` (`GW2Schedule.ae_of_ae_condExpKernel_on`),
  with no measurability of the record event needed.

* **`stageFieldLawXStatement`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Pt

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Sde GW2Sdh Supp8.GB6

/-- **RELDET's stage field law in law-transfer form** (`GW2Rd.StageFieldLawXStatement`), from `OpenLinesX.condGFF`. -/
theorem stageFieldLawXStatement : GW2Rd.StageFieldLawXStatement.{u} := by
  intro Ω _ _ I c r l x₀ hWm hO hβ hsort hHr A hA hnull
  obtain ⟨𝒢, M, hrec𝒢, -, -, hgff⟩ := hO.condGFF
  have hrec : Measurable (I.srecX c r l x₀) := hrec𝒢.mono 𝒢.2 le_rfl
  set T : Set Ω := {ω | (I.β (I.srecX c r l x₀ ω), I.Hr ω) ∈ A} with hTdef
  have hT : MeasurableSet T := ((hβ.comp hrec).prodMk hHr) hA
  have hconst := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := c.P) 𝒢.2 hrec𝒢
  -- the event is null under the kernel at almost every sample of the record event
  have hzero : ∀ᵐ ω₀ ∂c.P, I.srecX c r l x₀ ω₀ ∈ I.E → condExpKernel c.P 𝒢.1 ω₀ T = 0 := by
    filter_upwards [hgff, hconst] with ω₀ hg hc hE
    set b : BoundaryWord := I.β (I.srecX c r l x₀ ω₀) with hbdef
    have hTS : T =ᵐ[condExpKernel c.P 𝒢.1 ω₀] I.Hr ⁻¹' {g | (b, g) ∈ A} := hc.mono fun ω hω => by
      show ((I.β (I.srecX c r l x₀ ω), I.Hr ω) ∈ A) = ((b, I.Hr ω) ∈ A)
      rw [hω]
    have hAb : MeasurableSet {g : DistOn upperHalfPlaneOpens | (b, g) ∈ A} :=
      (measurable_const.prodMk measurable_id) hA
    rw [measure_congr hTS, ← Measure.map_apply hHr hAb]
    have hμ : IsGFFWithBoundaryData ((condExpKernel c.P 𝒢.1 ω₀).map I.Hr) id b.fn b.jumps :=
      Sec5.CfRegQ.isGFFWithBoundaryData_of_map_eq (hg hE) measurable_id (Measure.map_id.symm)
    have hP : IsProbabilityMeasure ((condExpKernel c.P 𝒢.1 ω₀).map I.Hr) :=
      (Measure.isProbabilityMeasure_map_iff hHr.aemeasurable).2 inferInstance
    have h0 := ae_iff.1 (hnull b (hsort _ hE) _ hP hμ)
    simpa only [not_not] using h0
  -- carry it to `P` through the `𝒢`-measurable event `{ν · T = 0}`
  have hL : MeasurableSet[𝒢.1] {ω₀ | condExpKernel c.P 𝒢.1 ω₀ T = 0} :=
    (Kernel.measurable_coe (condExpKernel c.P 𝒢.1) hT) (measurableSet_singleton 0)
  have hfin := GW2Schedule.ae_of_ae_condExpKernel_on (P := c.P) 𝒢.2 hL hT.compl
    (Eventually.of_forall fun ω₀ hω₀ => ae_iff.2 (by
      have e : {ω | ¬ω ∈ Tᶜ} = T := by ext ω; simp
      rw [e]
      exact hω₀))
  filter_upwards [hzero, hfin] with ω h1 h2 hE
  exact h2 (h1 hE)

end InteractingSLE.Theorem14.GW2Pt
