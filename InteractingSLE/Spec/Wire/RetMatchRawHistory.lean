/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchPredictLocal
import InteractingSLE.Spec.Exist.TransferHull

/-!
# Stopping times on the canonical killed-history space

The history reader recovers a continuous driving state before its lifetime.
Consequently the model's driving filtration is the usual augmentation of the
pullback of a single canonical history filtration. Doob–Dynkin then factors
finite stopping times through the history, preserving the stopping property.
This factorization does not assert the global Galmarino property.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchRaw

open Restart.RetAux79 Restart.FlowStopIdentG LawUnique Sec7.PocketTraversal

variable {nL nR : ℕ}

/-- The state reconstructed from a history has measurable killed observations. -/
theorem isMeasurableKilledDriving_history : IsMeasurableKilledDriving
    (fun t (γ : HistorySpace nL nR) => (histState γ t).1)
    (fun i t γ => (histState γ t).2.1 i)
    (fun j t γ => (histState γ t).2.2 j) Prod.fst := by
  intro r A hA
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurable_histState r) hA)

/-- The raw filtration of the reconstructed killed state on history space. -/
def historyFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (HistorySpace nL nR)) :=
  killedDrivingFiltration isMeasurableKilledDriving_history

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- For a continuous killed state, its driving filtration is the augmented
pullback of the canonical history filtration. -/
theorem drivingFiltration_eq_historyComap (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn
      (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      {t | (t : ℝ≥0∞) < V ω}) :
    drivingFiltration P hX = usualAugmentation
      (Exist.filtrationComap (killedHistory W VL VR V) (measurable_killedHistory hX)
        historyFiltration) P := by
  have hcomp := Exist.isMeasurableKilledDriving_comp isMeasurableKilledDriving_history
    (measurable_killedHistory hX)
  refine (Exist.drivingFiltration_congr_ae hX hcomp ?_).trans
    (Exist.drivingFiltration_comp isMeasurableKilledDriving_history (measurable_killedHistory hX) P)
  filter_upwards [hc] with ω hcω
  refine ⟨rfl, fun t ht => ?_⟩
  have he := histState_killedHistory hcω ht
  exact ⟨congrArg Prod.fst he,
    fun i => congrArg (fun s : DrivingValue nL nR => s.2.1 i) he,
    fun j => congrArg (fun s : DrivingValue nL nR => s.2.2 j) he⟩

/-- A finite stopping time of a continuous killed driving is almost surely a
finite stopping time on its canonical history space, with the image law. -/
theorem exists_isStoppingTime_ae_eq_history (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn
      (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω))
      {t | (t : ℝ≥0∞) < V ω})
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) σ)
    (hfin : ∀ᵐ ω ∂P, σ ω ≠ ⊤) :
    ∃ s : HistorySpace nL nR → ℝ≥0, Measurable s ∧
      IsStoppingTime (usualAugmentation historyFiltration (P.map (killedHistory W VL VR V)))
        (fun γ => (s γ : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂P, σ ω = (s (killedHistory W VL VR V ω) : WithTop ℝ≥0) := by
  have hσ' := drivingFiltration_eq_historyComap hX hc ▸ hσ
  obtain ⟨s, hs, he⟩ := Exist.exists_isStoppingTime_ae_eq_comp
    (measurable_killedHistory hX) rfl hσ' hfin
  have hsm : Measurable s := by
    apply measurable_of_Iic
    intro t
    convert (usualAugmentation historyFiltration (P.map (killedHistory W VL VR V))).le t _
      (hs t) using 1
    ext γ
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq, WithTop.coe_le_coe]
  exact ⟨s, hsm, hs, he⟩

end InteractingSLE.Wire.RetMatchRaw
