/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafFullLAlive

/-!
# Conditional means of the cutoff agree in full and killed filtrations

Galmarino's test makes the self-consistent cutoff a stopping time of the
full evolution filtration. Before the cutoff, the two filtrations have the
same event traces. After the cutoff, every Borel function of it is known.
These facts identify its conditional expectations at every fixed time.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF

/-- A self-consistent Galmarino cutoff is a stopping time of the full
continuation-driving filtration, including when the cutoff is infinite. -/
theorem isStoppingTime_full_of_galmarino_self
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞}
    (hXζ : IsMeasurableKilledDriving W VL VR ζ)
    (hXV : IsMeasurableKilledDriving W VL VR V) (hle : ∀ ω, V ω ≤ ζ ω)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω)
      {t | (t : ℝ≥0∞) < ζ ω})
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    (hself : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω)) :
    IsStoppingTime (drivingFiltration P hXζ) fun ω => (V ω : WithTop ℝ≥0) := by
  have he := ae_rule_full_eq_of_self hRg hc hle hself
  have hs := isStoppingTime_rule_of_ae_le_lifetime hXζ hRm hRg hc
    (he.mono fun ω hω => hω ▸ hle ω)
  have hVm := measurable_of_isMeasurableKilledDriving hXV
  intro t
  apply Restart.Aux54.measurableSet_usualAugmentation_of_ae_eq
    (measurableSet_le hVm measurable_const)
    ((drivingFiltration P hXζ).le t _ (hs t)) (hs t)
  filter_upwards [he] with ω hω
  change (V ω ≤ (t : ℝ≥0∞)) = (R (killedHistory W VL VR ζ ω) ≤ (t : ℝ≥0∞))
  rw [hω]

/-- For every integrable Borel function of the cutoff, conditioning on the
cutoff-driving filtration or the full driving filtration gives the same mean.
No continuous martingale or announcing sequence is assumed. -/
theorem condExp_cutoff_observable_eq_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞}
    (hXζ : IsMeasurableKilledDriving W VL VR ζ)
    (hXV : IsMeasurableKilledDriving W VL VR V) (hle : ∀ ω, V ω ≤ ζ ω)
    (hV : IsStoppingTime (drivingFiltration P hXζ) fun ω => (V ω : WithTop ℝ≥0))
    {f : ℝ≥0∞ → ℝ} (hf : Measurable f) (hi : Integrable (fun ω => f (V ω)) P)
    (t : ℝ≥0) :
    P[fun ω => f (V ω) | drivingFiltration P hXV t] =ᵐ[P]
      P[fun ω => f (V ω) | drivingFiltration P hXζ t] := by
  have hsub := drivingFiltration_le_of_earlier_stop hXζ hXV hV hle
  have hVown := Restart.Aux54.isStoppingTime_lifetime_driving (P := P) hXV
  have ha : MeasurableSet[drivingFiltration P hXV t] {ω | (t : ℝ≥0∞) < V ω} := by
    convert (hVown t).compl using 1
    ext ω
    change (t : ℝ≥0∞) < V ω ↔ ¬ V ω ≤ (t : ℝ≥0∞)
    exact not_le.symm
  have he : P[fun ω => f (V ω) | drivingFiltration P hXV t] =ᵐ[
      P.restrict {ω | (t : ℝ≥0∞) < V ω}]
      P[fun ω => f (V ω) | drivingFiltration P hXζ t] := by
    apply condExp_ae_eq_restrict_of_measurableSpace_eq_on
      ((drivingFiltration P hXV).le t) ((drivingFiltration P hXζ).le t) ha
    intro A
    constructor
    · exact hsub t _
    · intro hA
      have hm := measurableSet_driving_inter_alive hXζ hXV hle hA
      convert hm using 1
      ext ω
      simp only [mem_inter_iff]
      tauto
  have heI := (ae_eq_restrict_iff_indicator_ae_eq ((drivingFiltration P hXV).le t _ ha)).1 he
  have hdV := indicator_condExp_stopping_observable hVown hf hi t
  have hdζ := indicator_condExp_stopping_observable hV hf hi t
  filter_upwards [heI, hdV, hdζ] with ω hω hVω hζω
  by_cases hd : V ω ≤ (t : ℝ≥0∞)
  · rw [indicator_of_mem (show ω ∈ {ω | V ω ≤ (t : ℝ≥0∞)} from hd)] at hVω hζω
    exact hVω.trans hζω.symm
  · have hl : (t : ℝ≥0∞) < V ω := lt_of_not_ge hd
    simpa only [indicator_of_mem
      (show ω ∈ {ω | (t : ℝ≥0∞) < V ω} from hl)] using hω

end InteractingSLE.WFS
