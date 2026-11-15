/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootV7Model

/-!
# An actual slow-comparison window for each varying-angle model

The first-zero construction used for the numerical unit estimate also
supplies a witness for `HasSlowComparisonModels`. The comparison is only
on the slow event and survives every measurable buffer of the model.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR10

open GW2TipSystem GW2TipSystem.RootN4 GW2TipSystem.RootV7
  GW2TipSystem.RootL6 Sec5 Coupling

/-- Every actual varying-angle model admits an actual restart window whose
slow event is dominated by the model's buffered slow event. All stopping,
lifetime and drift data are constructed from its integrated evolution. -/
theorem exists_slowWindow {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL₀ nR₀ : ℕ} {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}
    (m : AngleModel.{u} κ ρL₀ ρR₀) :
    ∃ win : RootS5.RestartWindow.{u} κ (Prop59Stage.stageDriftBound κ ρL₀ ρR₀)
      (Icc (-angleWeightBound κ) (angleWeightBound κ)),
      win.e.P win.slowEvent ≤ m.law slowSet := by
  classical
  let e := m.e
  let : MeasurableSpace e.Ω := e.mΩ
  have : IsProbabilityMeasure e.P := m.hE.1.1.isGaussianProcess.isProbabilityMeasure
  let e' : EvolutionData.{u} (m.mL + nL₀) (m.mR + nR₀ + 1) :=
    { e with filtration := usualAugmentation e.filtration e.P }
  have hE' : e'.IsEvolution κ m.xL (angleWordL κ m.φ m.mL ρL₀)
      m.xR (angleWordR κ m.φ m.mR ρR₀) :=
    Ito.isIntegratedSLEEvolution_usualAugmentation m.hE
  let Good : e.Ω → Prop := fun ω =>
    IsIntegratedSLEPath κ m.xL m.xR (angleWordL κ m.φ m.mL ρL₀)
      (angleWordR κ m.φ m.mR ρR₀) (e.W · ω) (fun i t => e.VL i t ω)
      (fun i t => e.VR i t ω) (e.B · ω) (e.lifetime ω)
  let Gd : Set e.Ω := (toMeasurable e.P {ω | ¬ Good ω})ᶜ
  have hbad : e.P (toMeasurable e.P {ω | ¬ Good ω}) = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 m.hE.2.2.2.2
  have hGd : ∀ᵐ ω ∂e.P, ω ∈ Gd := by
    rw [ae_iff]
    change e.P Gdᶜ = 0
    simpa only [Gd, compl_compl] using hbad
  have hGood : ∀ ω ∈ Gd, Good ω := fun ω hω => by
    by_contra hn
    exact hω (subset_toMeasurable _ _ hn)
  have hGd0 : MeasurableSet[e'.filtration 0] Gd :=
    (Ito.measurableSet_usualAugmentation_of_null (𝓕 := e.filtration)
      (measurableSet_toMeasurable _ _) hbad 0).compl
  have hΦ : Continuous fun p : ℝ × (Fin (m.mL + nL₀) → ℝ) ×
      (Fin (m.mR + nR₀ + 1) → ℝ) => -(m.a + p.1) :=
    (continuous_const.add continuous_fst).neg
  obtain ⟨τ, hτ, hτG⟩ : ∃ τ : e.Ω → WithTop ℝ≥0,
      IsStoppingTime e'.filtration τ ∧ ∀ ω ∈ Gd,
        τ ω = hitBelow (fun t => -(m.a + e.W t ω)) (e.lifetime ω) 0 := by
    refine ⟨_, isStoppingTime_hitBelow_state hE'.2.1 hE'.2.2.1 hE'.2.2.2.1 hGd0
      (fun ω hω => by
        have hp := (hGood ω hω).isForcePath
        exact hp.continuousOn_w.prodMk ((continuousOn_pi.2 hp.continuousOn_vL).prodMk
          (continuousOn_pi.2 hp.continuousOn_vR))) hΦ 0, fun ω hω => ?_⟩
    simp only [hω, ↓reduceIte]
    rfl
  let A : Set e.Ω := {ω | τ ω < (e.lifetime ω : WithTop ℝ≥0)}
  have hζ : IsStoppingTime e'.filtration fun ω => (e.lifetime ω : WithTop ℝ≥0) :=
    Ito.isStoppingTime_lifetime hE'.2.1
  have hA : MeasurableSet[hτ.measurableSpace] A := by
    have heq : A = {ω | (e.lifetime ω : WithTop ℝ≥0) ≤ τ ω}ᶜ := by
      ext ω
      change τ ω < (e.lifetime ω : WithTop ℝ≥0) ↔
        ¬ (e.lifetime ω : WithTop ℝ≥0) ≤ τ ω
      exact not_le.symm
    rw [heq]
    exact (hζ.measurableSet_stopping_time_le hτ).compl
  have hAζ : ∀ ω ∈ A, (τ ω : ℝ≥0∞) < e'.lifetime ω := fun _ hω => hω
  have hhit : ∀ᵐ ω ∂e'.P, ω ∈ A → τ ω =
      hitBelow (fun t => -(m.a + e'.W t ω)) (e'.lifetime ω) 0 :=
    hGd.mono fun ω hω _ => hτG ω hω
  let win := restartWindowOfAngleWord hκ hκ4 ρL₀ ρR₀ m.mL m.mR m.φ m.hφ
    m.xL m.xR m.a m.hy e' hE' τ hτ A hA hAζ hhit
  refine ⟨win, ?_⟩
  rw [AngleModel.law, Measure.map_apply m.measurable_sample measurableSet_slowSet]
  have ha : m.a < 0 := by linarith only [m.hy.2.1]
  have hzero := ae_zero_of_first_passage e' hE' ha hAζ hhit
  refine measure_mono_ae (μ := e.P) ?_
  filter_upwards [hGd, hzero] with ω hωG hz hslow
  apply cutRecord_mem_slowSet
    (driverRecord_mem_slowSet_of_unit (xL := m.xL) (xR := m.xR) ?_) (m.buffer ω)
  intro q hq1 hqζ
  change ((q : ℝ≥0) : ℝ≥0∞) < e.lifetime ω at hqζ
  change m.a + ((Prop59Stage.samp (e.W · ω) (fun i t => e.VL i t ω)
    (fun i t => e.VR i t ω) (e.lifetime ω)).2 q).1 < 7 / 4
  rw [Prop59Stage.samp_snd_of_lt _ _ _ hqζ]
  change m.a + e.W q ω < 7 / 4
  have hτeq := hτG ω hωG
  by_cases hωA : ω ∈ A
  · have hfin : (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) = τ ω :=
      coe_untopA_of_ne_top (ne_top_of_lt (hAζ ω hωA))
    have hqNN : (q : ℝ≥0) < 1 := by exact_mod_cast hq1
    have hbefore : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.lifetime ω →
        t < (τ ω).untopA → m.a + e.W t ω ≤ 0 := by
      intro t ht htt
      exact Prop59Stage.le_zero_of_lt_hitBelow (a := m.a) ht (by
        rw [← hτeq, ← hfin]
        exact_mod_cast htt)
    exact RootS5.RestartWindow.driver_lt_of_mem_slowEvent win m.a hslow hbefore
      hz (fun hnA => False.elim (hnA hωA)) hqNN hqζ
  · have hle : (e.lifetime ω : WithTop ℝ≥0) ≤ τ ω := not_lt.1 hωA
    have hqt : ((q : ℝ≥0) : WithTop ℝ≥0) <
        hitBelow (fun t => -(m.a + e.W t ω)) (e.lifetime ω) 0 := by
      rw [← hτeq]
      exact lt_of_lt_of_le hqζ hle
    have hnonpos := Prop59Stage.le_zero_of_lt_hitBelow (a := m.a) hqζ hqt
    linarith only [hnonpos]

end InteractingSLE.Theorem14.GW2JDetR10
