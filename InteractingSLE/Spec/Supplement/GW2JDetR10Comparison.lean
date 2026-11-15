/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR10Records
import InteractingSLE.Spec.Supplement.GW2JDetR10Window
import InteractingSLE.Spec.Sec7.LocalExtNRef

/-!
# One-sided event comparisons on a stopped extension

A stopped extension already has the original probability law as its
projection. Live driver agreement and buffer protection give the two
event inequalities directly. Equality of full driving laws is unnecessary.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR10

open GW2TipSystem GW2TipSystem.RootN4 GW2TipSystem.RootV7 Sec5 Supp12.DSReach

/-- A continuous driver crossing above two gives a live rational crossing
of the physical sample. Agreement is needed only while both are alive. -/
theorem exists_liveCrossing_of_continuous_read {z : DriverRecord} {Y : ℝ≥0 → ℝ}
    {L : ℝ≥0∞} (hc : ContinuousOn Y {t | (t : ℝ≥0∞) < L})
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 →
      ((q : ℝ≥0) : ℝ≥0∞) < L → z.2 q = Y q)
    {t : ℝ≥0} (htz : (t : ℝ≥0∞) < z.1) (htL : (t : ℝ≥0∞) < L)
    (htY : 2 < Y t) : ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q := by
  have hcy : ContinuousOn Y {t | (t : ℝ≥0∞) < min L z.1} := by
    apply hc.mono
    intro t ht
    change (t : ℝ≥0∞) < min L z.1 at ht
    exact ht.trans_le (min_le_left _ _)
  have ht : (t : ℝ≥0∞) < min L z.1 := lt_min htL htz
  have hhit : Coupling.hitBelow (fun r => -(-2 + Y r)) (min L z.1) 0 <
      ((t + 1 : ℝ≥0) : WithTop ℝ≥0) :=
    (Coupling.hitBelow_le ht (show -(-2 + Y t) < 0 by linarith only [htY])).trans_lt
      (WithTop.coe_lt_coe.2 (lt_add_one t))
  obtain ⟨_, ⟨q, rfl⟩, _, hq, hY⟩ :=
    (Coupling.hitBelow_lt_iff (continuousOn_const.add hcy).neg
      LocalExt.dense_range_coe_nnrat (t + 1)).1 hhit
  refine ⟨q, hq.trans_le (min_le_right _ _), ?_⟩
  rw [hread q (hq.trans_le (min_le_right _ _)) (hq.trans_le (min_le_left _ _))]
  change -(-2 + Y q) < 0 at hY
  linarith only [hY]

/-- The slow comparison on an actual extension. The projection law comes
from the extension, while the only driver comparison is on the shorter
physical recording interval. The restart window itself is constructed. -/
theorem exists_slowWindow_on_extension {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL₀ nR₀ : ℕ} {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}
    (m : AngleModel.{u} κ ρL₀ ρR₀)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {π : m.e.Ω → Ω} (hπ : @Measurable _ _ m.e.mΩ _ π)
    (hmarginal : @Measure.map _ _ m.e.mΩ _ π m.e.P = μ) {sample : Ω → DriverRecord}
    (hsample : Measurable sample)
    (hstop : ∀ᵐ ξ ∂m.e.P, (sample (π ξ)).1 ≤ min (m.buffer ξ) (m.e.lifetime ξ))
    (hread : ∀ᵐ ξ ∂m.e.P, ∀ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < (sample (π ξ)).1 →
        (sample (π ξ)).2 q = m.a + m.e.W q ξ) :
    ∃ win : RootS5.RestartWindow.{u} κ (Prop59Stage.stageDriftBound κ ρL₀ ρR₀)
      (Icc (-angleWeightBound κ) (angleWeightBound κ)),
      win.e.P win.slowEvent ≤ (μ.map sample) slowSet := by
  let : MeasurableSpace m.e.Ω := m.e.mΩ
  obtain ⟨win, hwin⟩ := exists_slowWindow hκ hκ4 m
  refine ⟨win, hwin.trans ?_⟩
  rw [AngleModel.law, Measure.map_apply m.measurable_sample measurableSet_slowSet,
    Measure.map_apply hsample measurableSet_slowSet, ← hmarginal,
    Measure.map_apply hπ (hsample measurableSet_slowSet)]
  refine measure_mono_ae ?_
  filter_upwards [hstop, hread] with ξ hξstop hξread hξslow
  exact mem_slowSet_of_livePrefix hξstop (fun q hq =>
    (hξread q hq).trans (modelSample_read m.e m.a m.buffer ξ
      (hq.trans_le hξstop)).symm) hξslow

/-- A protected reference buffer crossing implies the physical crossing
on the same extension. The protection test uses the state path inside the
reference buffer, rather than assuming the desired crossing event. -/
theorem reach_probability_le_on_extension {κ a : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (e : EvolutionData.{u} nL nR) (hE : e.IsEvolution κ xL ρL xR ρR)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {π : e.Ω → Ω} (hπ : @Measurable _ _ e.mΩ _ π)
    (hmarginal : @Measure.map _ _ e.mΩ _ π e.P = μ) {sample : Ω → DriverRecord}
    (hsample : Measurable sample) (T : ℝ≥0)
    (O B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    (htarget : ∀ p ∈ O, 2 < a + p.1)
    (hprotect : ∀ᵐ ξ ∂e.P, ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < e.lifetime ξ →
      (∀ v ≤ t, Coupling.stateAt e.W e.VL e.VR v ξ ∈ B) →
        (t : ℝ≥0∞) < (sample (π ξ)).1)
    (hread : ∀ᵐ ξ ∂e.P, ∀ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < (sample (π ξ)).1 →
      ((q : ℝ≥0) : ℝ≥0∞) < e.lifetime ξ →
        (sample (π ξ)).2 q = a + e.W q ξ) :
    e.P (reachEvent T O B e.W e.VL e.VR e.lifetime) ≤ (μ.map sample)
      {z | ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q} := by
  let : MeasurableSpace e.Ω := e.mΩ
  rw [Measure.map_apply hsample measurableSet_liveCrossing, ← hmarginal,
    Measure.map_apply hπ (hsample measurableSet_liveCrossing)]
  refine measure_mono_ae ?_
  filter_upwards [hE.2.2.2.2, hprotect, hread] with ξ hp hξprotect hξread hξreach
  obtain ⟨t, htT, htL, htO, htB⟩ := hξreach
  exact exists_liveCrossing_of_continuous_read
    (continuousOn_const.add hp.isForcePath.continuousOn_w) hξread
    (hξprotect t htT htL htB) htL (htarget _ htO)

end InteractingSLE.Theorem14.GW2JDetR10
