/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPastGFiltration

/-!
# Continuous driving-adapted processes are raw-past measurable at positive times

Approach the present from strictly earlier times. The strict filtration
inclusion proved above and path continuity yield measurability for the
completed raw past. Time zero is treated separately by its scalar value.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- Any continuous driving-adapted process is measurable for the completed raw
past at a positive time. No martingale or closing identity is required. -/
theorem measurable_process_rawPast_of_pos
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hn : ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0)
    {X : ℝ≥0 → Ω → ℝ} (hA : StronglyAdapted (drivingFiltration P hX) X)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω)) {t : ℝ≥0} (ht : 0 < t) :
    Measurable[samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P] (X t) := by
  obtain ⟨u, _, hu, hlim⟩ := exists_seq_strictMono_tendsto' ht
  have hm : StronglyMeasurable[samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P]
      (fun ω => limUnder atTop fun n => X (u n) ω) :=
    @StronglyMeasurable.limUnder ℕ Ω ℝ
      (samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P) _ _ atTop _
      (fun n ω => X (u n) ω) _ _ (fun n => (hA (u n)).mono (drivingFiltration_le_rawPast hX hc hn (hu n).2))
  apply Sec2.Restart.measurable_of_ae_eq_of_null
    (sup_le (samplePastSigma_le (measurable_killedHistory hX) t)
      (MeasurableSpace.generateFrom_le fun _ hs => hs.1))
    (fun A hAm hA0 => (le_sup_right : nullSigma P ≤
      samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P)
      A (MeasurableSpace.measurableSet_generateFrom ⟨hAm, hA0⟩)) hm.measurable
    ((hA t).measurable.mono ((drivingFiltration P hX).le t) le_rfl)
  filter_upwards [hcont] with ω hω
  exact ((hω.tendsto t).comp hlim).limUnder_eq

/-- An a.e. constant initial value handles the only time not covered by the
strict-time approximation. -/
theorem measurable_process_rawPast_of_initial
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hn : ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0)
    {X : ℝ≥0 → Ω → ℝ} (hA : StronglyAdapted (drivingFiltration P hX) X)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hinit : ∃ c : ℝ, X 0 =ᵐ[P] fun _ => c) (t : ℝ≥0) :
    Measurable[samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P] (X t) := by
  by_cases ht : t = 0
  · subst t
    obtain ⟨c, hc0⟩ := hinit
    exact Sec2.Restart.measurable_of_ae_eq_of_null
      (sup_le (samplePastSigma_le (measurable_killedHistory hX) 0)
        (MeasurableSpace.generateFrom_le fun _ hs => hs.1))
      (fun A hAm hA0 => (le_sup_right : nullSigma P ≤
        samplePastSigma (killedHistory W VL VR V) 0 ⊔ nullSigma P)
        A (MeasurableSpace.measurableSet_generateFrom ⟨hAm, hA0⟩)) measurable_const
      ((hA 0).measurable.mono ((drivingFiltration P hX).le 0) le_rfl) hc0.symm
  · exact measurable_process_rawPast_of_pos hX hc hn hA hcont (pos_iff_ne_zero.2 ht)

/-- The full raw-past conditional-expectation comparison follows from a
continuous closed process and an a.e. constant initial value. -/
theorem condExp_driving_eq_rawPast_of_initial [IsFiniteMeasure P]
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hn : ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0)
    {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}
    (hA : StronglyAdapted (drivingFiltration P hX) X)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hinit : ∃ c : ℝ, X 0 =ᵐ[P] fun _ => c)
    (hclosed : ∀ t, X t =ᵐ[P] P[Z | drivingFiltration P hX t]) (t : ℝ≥0) :
    P[Z | drivingFiltration P hX t] =ᵐ[P]
      P[Z | samplePastSigma (killedHistory W VL VR V) t] := by
  have hXi : Integrable (X t) P := integrable_condExp.congr (hclosed t).symm
  have hXm := measurable_process_rawPast_of_initial hX hc hn hA hcont hinit t
  have hfix : P[X t | samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P] = X t :=
    condExp_of_stronglyMeasurable
      (sup_le (samplePastSigma_le (measurable_killedHistory hX) t)
        (MeasurableSpace.generateFrom_le fun _ hs => hs.1)) hXm.stronglyMeasurable hXi
  have he : P[X t | samplePastSigma (killedHistory W VL VR V) t] =ᵐ[P] X t := by
    have h := MathFin.ItoLocalMartingale.condExp_sup_nulls
      (samplePastSigma_le (measurable_killedHistory hX) t) hXi
    change P[X t | samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P] =ᵐ[P]
      P[X t | samplePastSigma (killedHistory W VL VR V) t] at h
    rw [hfix] at h
    exact h.symm
  have hpost := (condExp_congr_ae (m := samplePastSigma (killedHistory W VL VR V) t) (hclosed t)).trans
    (condExp_condExp_of_le (samplePastSigma_le_drivingFiltration hX t) ((drivingFiltration P hX).le t))
  exact (hclosed t).symm.trans (he.symm.trans hpost)

end InteractingSLE.WFS
