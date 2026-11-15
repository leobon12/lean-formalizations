/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafCylKAssembly

/-!
# Full driving events restricted to survival

A full-filtration event at time `t`, restricted to `t < V`, is measurable in
the cutoff filtration at `t`. Conversely, a function of a stopping time is
already known on the event that this stopping time has occurred.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

/-- Full and cutoff events have the same trace on the survival event.
This direction needs only measurable killed coordinates and `V ≤ ζ`. -/
theorem measurableSet_driving_inter_alive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞}
    (hXζ : IsMeasurableKilledDriving W VL VR ζ)
    (hXV : IsMeasurableKilledDriving W VL VR V) (hle : ∀ ω, V ω ≤ ζ ω)
    {t : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[drivingFiltration P hXζ t] A) :
    MeasurableSet[drivingFiltration P hXV t] (A ∩ {ω | (t : ℝ≥0∞) < V ω}) := by
  have hAm := (drivingFiltration P hXζ).le t A hA
  have hlive : MeasurableSet {ω | (t : ℝ≥0∞) < V ω} :=
    measurableSet_lt measurable_const (measurable_of_isMeasurableKilledDriving hXV)
  change MeasurableSet[usualAugmentation (killedDrivingFiltration hXV) P t] _
  rw [Ito.usualAugmentation_apply]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro s hts
  obtain ⟨q, _, hq, hlim⟩ := exists_seq_strictAnti_tendsto' hts
  have hex : ∀ n, ∃ C : Set Ω, MeasurableSet[killedDrivingFiltration hXV (q n)] C ∧
      C =ᵐ[P] A ∩ {ω | (q n : ℝ≥0∞) < V ω} := by
    intro n
    obtain ⟨B, hB, hAB⟩ := Ito.exists_ae_eq_of_measurableSet_usualAugmentation (hq n).1 hA
    refine ⟨B ∩ {ω | (q n : ℝ≥0∞) < V ω},
      measurableSet_killedDrivingSigma_inter_lt hle hB, ?_⟩
    filter_upwards [hAB] with ω hω
    change (ω ∈ B ∧ (q n : ℝ≥0∞) < V ω) =
      (ω ∈ A ∧ (q n : ℝ≥0∞) < V ω)
    rw [← hω]
  choose C hC he using hex
  have hCm : MeasurableSet[killedDrivingFiltration hXV s] (liminf C atTop) :=
    @MeasurableSet.measurableSet_liminf Ω (killedDrivingFiltration hXV s) C fun n =>
      (killedDrivingFiltration hXV).mono (hq n).2.le _ (hC n)
  apply Coupling.measurableSet_nullAugmented_of_ae_eq (hAm.inter hlive) hCm
  filter_upwards [ae_all_iff.2 he] with ω hω
  apply propext
  rw [mem_liminf_iff_eventually_mem]
  constructor
  · rintro ⟨hωA, htV⟩
    obtain ⟨v, htv, hvV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htV
    have hev := hlim.eventually (Iio_mem_nhds (ENNReal.coe_lt_coe.1 htv))
    filter_upwards [hev] with n hn
    exact (Iff.of_eq (hω n)).2 ⟨hωA, (ENNReal.coe_lt_coe.2 hn).trans hvV⟩
  · intro hmem
    obtain ⟨n, hn⟩ := hmem.exists
    have hnA := (Iff.of_eq (hω n)).1 hn
    exact ⟨hnA.1, (ENNReal.coe_lt_coe.2 (hq n).1).trans hnA.2⟩

/-- A Borel function of a stopping time, masked off until it has occurred,
is measurable at the current deterministic time. -/
theorem measurable_indicator_stopping_observable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓓 : Filtration ℝ≥0 mΩ}
    {V : Ω → ℝ≥0∞} (hV : IsStoppingTime 𝓓 fun ω => (V ω : WithTop ℝ≥0))
    {f : ℝ≥0∞ → ℝ} (hf : Measurable f) (t : ℝ≥0) :
    Measurable[𝓓 t] ({ω | V ω ≤ (t : ℝ≥0∞)}.indicator fun ω => f (V ω)) := by
  have hmin : Measurable[𝓓 t] (fun ω => min (V ω) (t : ℝ≥0∞)) :=
    (hV.min_const t).measurable.mono
      ((hV.min_const t).measurableSpace_le_of_le_const fun _ => min_le_right _ _) le_rfl
  have he : {ω | V ω ≤ (t : ℝ≥0∞)}.indicator (fun ω => f (V ω)) =
      {ω | V ω ≤ (t : ℝ≥0∞)}.indicator (fun ω => f (min (V ω) t)) := by
    apply Set.indicator_congr
    intro ω hω
    change f (V ω) = f (min (V ω) (t : ℝ≥0∞))
    rw [min_eq_left (show V ω ≤ (t : ℝ≥0∞) from hω)]
  rw [he]
  exact (hf.comp hmin).indicator (hV t)

/-- Once a stopping time has occurred, its integrable Borel observable
agrees with its conditional expectation at that time. -/
theorem indicator_condExp_stopping_observable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓓 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞}
    (hV : IsStoppingTime 𝓓 fun ω => (V ω : WithTop ℝ≥0))
    {f : ℝ≥0∞ → ℝ} (hf : Measurable f) (hi : Integrable (fun ω => f (V ω)) P)
    (t : ℝ≥0) :
    ({ω | V ω ≤ (t : ℝ≥0∞)}.indicator P[fun ω => f (V ω) | 𝓓 t]) =ᵐ[P]
      {ω | V ω ≤ (t : ℝ≥0∞)}.indicator (fun ω => f (V ω)) := by
  have he := condExp_indicator hi (hV t)
  have hfix := condExp_of_stronglyMeasurable (𝓓.le t)
    (measurable_indicator_stopping_observable hV hf t).stronglyMeasurable
    (hi.indicator ((𝓓.le t) _ (hV t)))
  exact he.symm.trans (Filter.EventuallyEq.of_eq hfix)

end InteractingSLE.WFS
