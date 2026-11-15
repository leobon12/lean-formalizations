/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverObservable

/-!
# A single driving-lifetime announcement supplies both stopped-K2 sequences

Packet PROVE-RETPLUMB. The announcement is needed under the conditional model
law. A supported lifetime is zero off its initial event, so an announcement
under the original law would generally be impossible there.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Sec7.PocketTraversal DomainMarkov FCDet
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Exact remaining predictability input for the killed driving lifetime.
This is a named proposition, not an assertion that every killed lifetime is
predictable. In the retained application `P` is the law conditioned on a type. -/
def RetDrivingLifetimePredictable {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (P : Measure Ω) (hX : IsMeasurableKilledDriving W VL VR V) : Prop :=
  ∃ T : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq (drivingFiltration P hX) P V T

/-- Strictly announcing a lifetime forces that lifetime to be positive almost
surely. This explains why supported lifetimes must use the conditional law. -/
theorem ae_pos_of_isAnnouncingSeq {𝓕 : Filtration ℝ≥0 mΩ}
    {V : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} (hT : Coupling.IsAnnouncingSeq 𝓕 P V T) :
    ∀ᵐ ω ∂P, 0 < V ω := by
  filter_upwards [hT.2.2.1 0] with ω hω
  exact lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ T 0 ω) hω

/-- An announcing sequence converges to its lifetime in the extended topology. -/
theorem ae_tendsto_of_isAnnouncingSeq {𝓕 : Filtration ℝ≥0 mΩ}
    {V : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} (hT : Coupling.IsAnnouncingSeq 𝓕 P V T) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (T n ω : ℝ≥0∞)) atTop (𝓝 (V ω)) := by
  filter_upwards [ae_all_iff.2 hT.2.2.1, hT.2.2.2] with ω hlt hex
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨t, hat, htV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    obtain ⟨N, hN⟩ := hex t htV
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hat.trans_le (ENNReal.coe_le_coe.2 (hN.trans (hT.2.1 ω hn)))
  · intro a ha
    exact Eventually.of_forall fun n => (hlt n).trans ha

/-- The driving filtration of the stopped geometric coordinates is contained
in the augmented capacity filtration, using adaptedness alone. -/
theorem drivingFiltration_geom_le_usual {𝓗 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {V : Ω → ℝ≥0∞} (hWa : StronglyAdapted 𝓗 W)
    (hWc : ∀ ω, Continuous fun t => W t ω)
    (hxL : Measurable[𝓗 0] xL) (hxR : Measurable[𝓗 0] xR)
    (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t}) :
    drivingFiltration P (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs) ≤
      usualAugmentation 𝓗 P :=
  Ito.usualAugmentation_mono
    (Ito.killedDrivingFiltration_le (MartChar.adaptedBefore_of_stronglyAdapted hVs hWa)
      (fun i => MartChar.adaptedBefore_of_stronglyAdapted hVs (stronglyAdapted_geomLW hWa hWc hxL i))
      (fun j => MartChar.adaptedBefore_of_stronglyAdapted hVs (stronglyAdapted_geomRW hWa hWc hxR j))
      (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs)) P

/-- One driving announcement supplies the augmented announcement and the
monotone driving stops, with strict inequality and convergence, required by K2. -/
theorem exists_stoppedK2_sequences {𝓗 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {V : Ω → ℝ≥0∞} (hWa : StronglyAdapted 𝓗 W)
    (hWc : ∀ ω, Continuous fun t => W t ω)
    (hxL : Measurable[𝓗 0] xL) (hxR : Measurable[𝓗 0] xR)
    (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t})
    (hp : RetDrivingLifetimePredictable P (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs)) :
    ∃ T : ℕ → Ω → ℝ≥0,
      Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P V T ∧
      (∀ n, IsStoppingTime
        (drivingFiltration P (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs))
        (fun ω => (T n ω : WithTop ℝ≥0))) ∧
      (∀ ω, Monotone fun n => (T n ω : WithTop ℝ≥0)) ∧
      (∀ᵐ ω ∂P, ∀ n, (T n ω : ℝ≥0∞) < V ω) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => (T n ω : ℝ≥0∞)) atTop (𝓝 (V ω)) := by
  obtain ⟨T, hT⟩ := hp
  refine ⟨T, isAnnouncingSeq_of_absolutelyContinuous hT
    (drivingFiltration_geom_le_usual hWa hWc hxL hxR hVs) Measure.AbsolutelyContinuous.rfl,
    hT.1, ?_, ae_all_iff.2 hT.2.2.1, ae_tendsto_of_isAnnouncingSeq hT⟩
  intro ω n k hnk
  exact WithTop.coe_le_coe.2 (hT.2.1 ω hnk)

end InteractingSLE.Restart.RetAux79
