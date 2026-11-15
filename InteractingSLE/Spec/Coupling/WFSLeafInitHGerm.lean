/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPastGAssembly

/-!
# Positive killing preserves the initial driving germ

Raw cutoff events have full-history representatives on the alive event. Along
times decreasing to zero these representatives eventually agree with the given
event, since the cutoff is positive. Their set liminf gives the full germ event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

/-- At time zero, a strictly positive cutoff adds no information to the full
usual driving augmentation. No announcing sequence or rule is required. -/
theorem drivingFiltration_zero_le_full_of_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞}
    (hXζ : IsMeasurableKilledDriving W VL VR ζ)
    (hXV : IsMeasurableKilledDriving W VL VR V)
    (hVζ : ∀ ω, V ω ≤ ζ ω) (hpos : ∀ᵐ ω ∂P, 0 < V ω) :
    drivingFiltration P hXV 0 ≤ drivingFiltration P hXζ 0 := by
  intro A hA
  have hAm := (drivingFiltration P hXV).le 0 A hA
  change MeasurableSet[usualAugmentation (killedDrivingFiltration hXζ) P 0] A
  rw [Ito.usualAugmentation_apply]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro t ht
  obtain ⟨q, _, hq, hlim⟩ := exists_seq_strictAnti_tendsto' ht
  have hex : ∀ n, ∃ C : Set Ω,
      MeasurableSet[killedDrivingFiltration hXζ (q n)] C ∧
      ∀ᵐ ω ∂P, (q n : ℝ≥0∞) < V ω → (ω ∈ A ↔ ω ∈ C) := by
    intro n
    obtain ⟨E, hE, hAE⟩ :=
      Ito.exists_ae_eq_of_measurableSet_usualAugmentation (hq n).1 hA
    obtain ⟨C, hC, hEC⟩ := exists_measurableSet_killedDrivingSigma_eqOn hVζ hE
    exact ⟨C, hC, hAE.mono fun ω hω hqV => (Iff.of_eq hω).trans (hEC ω hqV)⟩
  choose C hC hAC using hex
  have hCm : MeasurableSet[killedDrivingFiltration hXζ t] (liminf C atTop) :=
    @MeasurableSet.measurableSet_liminf Ω (killedDrivingFiltration hXζ t) C fun n =>
      (killedDrivingFiltration hXζ).mono (hq n).2.le _ (hC n)
  apply Coupling.measurableSet_nullAugmented_of_ae_eq hAm hCm
  filter_upwards [hpos, ae_all_iff.2 hAC] with ω hω hrep
  obtain ⟨v, hv0, hvV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hω
  have hvpos : (0 : ℝ≥0) < v := ENNReal.coe_lt_coe.1 hv0
  have hev := (hlim.eventually (Iio_mem_nhds hvpos)).mono
    (fun n hn => hrep n ((ENNReal.coe_lt_coe.2 hn).trans hvV))
  apply propext
  rw [mem_liminf_iff_eventually_mem]
  constructor
  · intro hωA
    exact hev.mono fun _ h => h.mp hωA
  · intro hCω
    obtain ⟨n, hn, hnC⟩ := (hev.and hCω).exists
    exact hn.mpr hnC

end InteractingSLE.WFS
