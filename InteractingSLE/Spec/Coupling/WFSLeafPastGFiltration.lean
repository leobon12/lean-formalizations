/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPastGDecode

/-!
# Strictly earlier driving sigma algebras belong to a later raw past

The raw state reader and the recovered lifetime tests generate the killed
driving filtration at every earlier time. Choosing an intermediate time also
handles its usual augmentation.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.FlowStopIdentG

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- Every earlier generator of the killed driving sigma algebra is observable
from a later raw sample past, after adjoining null sets. -/
theorem measurableSet_state_rawPast
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hn : ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0)
    {r t : ℝ≥0} (hrt : r < t) (A : Set (DrivingValue nL nR)) (hA : MeasurableSet A) :
    MeasurableSet[samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P]
      {ω | (r : ℝ≥0∞) < V ω ∧ (W r ω, (fun i => VL i r ω), fun i => VR i r ω) ∈ A} := by
  apply ZhanGT4.A1Canon.measurableSet_of_ae_eq_of_nullSets_le
    (sup_le (samplePastSigma_le (measurable_killedHistory hX) t)
      (MeasurableSpace.generateFrom_le fun _ hs => hs.1)) le_sup_right (hX r A hA)
    ((measurableSet_live_rawPast hX hn hrt).inter
      (((measurable_histState_rawPast (killedHistory W VL VR V) hrt.le).mono le_sup_left le_rfl) hA))
  filter_upwards [hc] with ω hω
  change ((r : ℝ≥0∞) < V ω ∧ (W r ω, (fun i => VL i r ω), fun i => VR i r ω) ∈ A) =
    ((r : ℝ≥0∞) < V ω ∧ histState (killedHistory W VL VR V ω) r ∈ A)
  by_cases hr : (r : ℝ≥0∞) < V ω
  · rw [histState_killedHistory hω hr]
  · simp only [hr, false_and]

/-- The raw killed-driving filtration at `s<t` is contained in the completed
raw sample past at `t`. -/
theorem killedDrivingFiltration_le_rawPast
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hn : ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0)
    {s t : ℝ≥0} (hst : s < t) :
    killedDrivingFiltration hX s ≤ samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P := by
  apply MeasurableSpace.generateFrom_le
  rintro E ⟨r, hrs, A, hA, rfl⟩
  exact measurableSet_state_rawPast hX hc hn (hrs.trans_lt hst) A hA

/-- The same strict-time inclusion holds after usual augmentation. -/
theorem drivingFiltration_le_rawPast
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hn : ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0)
    {s t : ℝ≥0} (hst : s < t) :
    drivingFiltration P hX s ≤ samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P := by
  obtain ⟨u, hsu, hut⟩ := exists_between hst
  change usualAugmentation (killedDrivingFiltration hX) P s ≤ _
  rw [Ito.usualAugmentation_apply]
  refine (iInf₂_le u hsu).trans ?_
  exact sup_le (killedDrivingFiltration_le_rawPast hX hc hn hut) le_sup_right

/-- Conversely the raw samples through `t` are adapted to the driving filtration
at `t`, without any nonzero-sample or continuity assumption. -/
theorem samplePastSigma_le_drivingFiltration
    (hX : IsMeasurableKilledDriving W VL VR V) (t : ℝ≥0) :
    samplePastSigma (killedHistory W VL VR V) t ≤ drivingFiltration P hX t := by
  have hm : Measurable[drivingFiltration P hX t]
      (fun ω => samplePast t (killedHistory W VL VR V ω)) := by
    apply (@measurable_pi_iff Ω (ℕ × ℕ) (fun _ => DrivingValue nL nR)
      (drivingFiltration P hX t) _ _).2
    intro p
    by_cases hp : dyadicTime p ≤ t
    · simp only [samplePast, hp, ↓reduceIte]
      exact (Sec4.measurable_killedSample hX p).mono
        (((killedDrivingFiltration hX).mono hp).trans (Ito.le_usualAugmentation _ P t)) le_rfl
    · simp only [samplePast, hp, ↓reduceIte]
      exact measurable_const
  exact hm.comap_le

end InteractingSLE.WFS
