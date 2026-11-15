/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BRLeafGB6
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# Corollary BR4a: the field half (the canonical centred counterflow pair of the recentred field)

Packet PROVE-BR4A. Corollary BR4a (supplement p. 610) reads the field `h` in the frame recentred at `v`
("This calculation retains the original literal or centered field frame; no new additive constant is chosen"):

* `recField v h = h(· + v)` (`Exist.flowField v 0`), with `IsChartTransport (Chart.id.recenter v) 1 0 k h hv` for
  every lift coefficient `k` (the recentring chart has lift `0`): `isChartTransport_recField`;
* its return field is a GFF with an explicit word (`exists_word_recField`: the recentred word
  `Exist.StagedLaw.BoundaryWord.shiftW v c` of a word `c` of `(b, jumps)`, then the return transport);
* **`exists_isCenteredCounterflowDriver_recField`**: the field-determined driver of Theorem 1.2 for that word
  (`BRLeaf.cfDrv`) is a frozen centred counterflow driver of `recField v h` (`BRLeaf.isCenteredCounterflowDriver_cfDrv`,
  PROVE-T14-BR).

Theorems 1.2–1.3 (at the universe of the sample space) are hypotheses; this serves Theorem 1.4 (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BR4aPath

open Restart Sec7.StripSysField

/-- **The field read in the frame recentred at `v`**: `h(· + v)`, no new additive constant. -/
def recField (v : ℝ) (h : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens := Exist.flowField v 0 h

theorem measurable_recField (v : ℝ) : Measurable (recField v) := Exist.measurable_flowField v 0

/-- **The recentred field is the recentring transport of `h`**, for every lift coefficient (the lift is `0`). -/
theorem isChartTransport_recField (k v : ℝ) (h : DistOn upperHalfPlaneOpens) :
    IsChartTransport (Chart.id.recenter v) 1 0 k h (recField v h) := by
  have hℓ : MeasureTheory.LocallyIntegrableOn
      (fun w => (Exist.shiftChart v).2.2 ((Exist.shiftChart v).2.1 w)) H := by
    have : (fun w => (Exist.shiftChart v).2.2 ((Exist.shiftChart v).2.1 w)) = fun _ => (0 : ℝ) := rfl
    rw [this]
    exact MeasureTheory.locallyIntegrableOn_const 0
  have htr := Chart.isChartTransport_chartTransport (Exist.isConformal_shiftChart v) hℓ 1 0 0 h
  intro φ φ' hs hφ
  have h1 := htr φ φ' hs hφ
  have h2 : recField v h φ' = Chart.chartTransport (Exist.isConformal_shiftChart v) 1 0 0 h φ' := rfl
  rw [h2, h1]
  simp [Exist.shiftChart, Chart.recenter, Chart.id]

/-- **The return field of the recentred field is a GFF with an explicit word.** -/
theorem exists_word_recField {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) (v : ℝ) :
    ∃ β : BoundaryWord, IsGFFWithBoundaryData P
      (fun ω => returnField (Real.pi * chiC κ) (chiC κ) (recField v (h ω))) β.fn β.jumps := by
  obtain ⟨c, hcJ, hcb⟩ := BoundaryWord.exists_fn_eq hb
  have hc : IsGFFWithBoundaryData P h c.fn c.jumps := (BoundaryWord.isGFFWithBoundaryData_fn_iff hcJ hcb P h).2 hh
  have h1 := Exist.StagedLaw.isGFFWithBoundaryData_shiftW v hc
  set c' := Exist.StagedLaw.BoundaryWord.shiftW v c with hc'
  obtain ⟨u₁, hu₁, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c'.isPiecewiseConstantBoundaryData
  have h2 := isGFFWithBoundaryData_returnField (Real.pi * chiC κ) (chiC κ) ⟨u₁, hu₁⟩ h1
  have hb2 := isPiecewiseConstant_returnData (Real.pi * chiC κ) (chiC κ) c'.isPiecewiseConstantBoundaryData
  obtain ⟨β, hβJ, hβb⟩ := BoundaryWord.exists_fn_eq hb2
  exact ⟨β, (BoundaryWord.isGFFWithBoundaryData_fn_iff hβJ hβb P _).2 h2⟩

/-- **The canonical centred counterflow pair of the recentred field** (the field half of Corollary BR4a): the
field-determined driver of Theorem 1.2 for the counterflow word of the recentred field drives the frozen centred
counterflow of `recField v h`. -/
theorem exists_isCenteredCounterflowDriver_recField (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J) (v : ℝ) :
    ∃ (Wv : ℝ≥0 → Ω → ℝ) (ζv : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P (fun ω => recField v (h ω)) Wv ζv := by
  obtain ⟨β, hβ⟩ := exists_word_recField (κ := κ) hb hh v
  have hk : 0 < 16 / κ := by positivity
  exact ⟨_, _, BRLeaf.isCenteredCounterflowDriver_cfDrv h12p h13 hκ hk ((measurable_recField v).comp hh.1) hβ⟩

end InteractingSLE.Theorem14.BR4aPath
