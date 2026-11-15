/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootL6Window
import InteractingSLE.Spec.Supplement.GW2RootS5Delay

/-!
# A uniform unit premise for arbitrary varying-angle words

Continuation of PROVE-T14-GW2ROOT2. The first-zero stopping time and its
event are constructed in the usual augmentation. The resulting unit
estimate is uniform in all angle values and block lengths, and needs no
trace hypothesis. It supplies the finite-force slow estimate; identifying
the root's retained law with this word is still a separate task.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootL6

open RootN4 Sec5 Coupling

/-- Killing the rational observations earlier preserves the unit event.
This abstracts the existing far-lifetime comparison to any smaller lifetime. -/
theorem mem_unitSet_of_lifetime_le {nL nR : ℕ}
    {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {ζ ζ' : ℝ≥0∞} (hle : ζ' ≤ ζ)
    (hunit : ((a, xL, xR), Prop59Stage.samp w vL vR ζ) ∈ Prop59Stage.unitSet) :
    ((a, xL, xR), Prop59Stage.samp w vL vR ζ') ∈ Prop59Stage.unitSet := by
  intro q hq1 hqζ'
  change ((q : ℝ≥0) : ℝ≥0∞) < ζ' at hqζ'
  have hqζ := hqζ'.trans_le hle
  have h := hunit q hq1 hqζ
  change a + ((Prop59Stage.samp w vL vR ζ).2 q).1 < 7 / 4 at h
  change a + ((Prop59Stage.samp w vL vR ζ').2 q).1 < 7 / 4
  rw [Prop59Stage.samp_snd_of_lt _ _ _ hqζ']
  rw [Prop59Stage.samp_snd_of_lt _ _ _ hqζ] at h
  exact h

/-- The positive unit probability depends only on `κ` and the inherited
weights. Every integrated evolution of the varying-angle word from a
separated admissible start satisfies the sampled slow bound. The proof
constructs all stopping-time data needed by `restartWindowOfAngleWord`. -/
theorem exists_uniform_unit_bound {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL₀ nR₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ (mL mR : ℕ) (φ : ℕ → ℝ),
      (∀ i, φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) →
      ∀ (xL : Fin (mL + nL₀) → ℝ) (xR : Fin (mR + nR₀ + 1) → ℝ) (a : ℝ),
      (a, xL, xR) ∈ Prop59Stage.startsU →
      ∀ e : EvolutionData.{u} (mL + nL₀) (mR + nR₀ + 1),
      e.IsEvolution κ xL (angleWordL κ φ mL ρL₀) xR (angleWordR κ φ mR ρR₀) →
      ENNReal.ofReal p₀ ≤ e.P {ω |
        ((a, xL, xR), Prop59Stage.samp (e.W · ω) (fun i t => e.VL i t ω)
          (fun i t => e.VR i t ω) (e.lifetime ω)) ∈ Prop59Stage.unitSet} := by
  classical
  have hJ2 : Icc (-angleWeightBound κ) (angleWeightBound κ) ⊆ Ioi (-2) := by
    intro x hx
    have hM := angleWeightBound_lt_two hκ
    exact show -2 < x by linarith only [hx.1, hM]
  obtain ⟨p₀, hp₀, hp₀1, hbound⟩ := RootS5.exists_uniform_slow_probability
    (C := Prop59Stage.stageDriftBound κ ρL₀ ρR₀) hκ isCompact_Icc hJ2
  refine ⟨p₀, hp₀, hp₀1, ?_⟩
  intro mL mR φ hφ xL xR a hy e hE
  let : MeasurableSpace e.Ω := e.mΩ
  have : IsProbabilityMeasure e.P := hE.1.1.isGaussianProcess.isProbabilityMeasure
  let e' : EvolutionData.{u} (mL + nL₀) (mR + nR₀ + 1) :=
    { e with filtration := usualAugmentation e.filtration e.P }
  have hE' : e'.IsEvolution κ xL (angleWordL κ φ mL ρL₀)
      xR (angleWordR κ φ mR ρR₀) := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  let Good : e.Ω → Prop := fun ω =>
    IsIntegratedSLEPath κ xL xR (angleWordL κ φ mL ρL₀) (angleWordR κ φ mR ρR₀)
      (e.W · ω) (fun i t => e.VL i t ω) (fun i t => e.VR i t ω)
      (e.B · ω) (e.lifetime ω)
  let Gd : Set e.Ω := (toMeasurable e.P {ω | ¬ Good ω})ᶜ
  have hbad : e.P (toMeasurable e.P {ω | ¬ Good ω}) = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 hE.2.2.2.2
  have hGd : ∀ᵐ ω ∂e.P, ω ∈ Gd := by
    rw [ae_iff]
    change e.P Gdᶜ = 0
    simpa only [Gd, compl_compl] using hbad
  have hGdGood : ∀ ω ∈ Gd, Good ω := fun ω hω => by
    by_contra hnot
    exact hω (subset_toMeasurable _ _ hnot)
  have hGd0 : MeasurableSet[e'.filtration 0] Gd :=
    (Ito.measurableSet_usualAugmentation_of_null (𝓕 := e.filtration)
      (measurableSet_toMeasurable _ _) hbad 0).compl
  have hΦ : Continuous fun p : ℝ × (Fin (mL + nL₀) → ℝ) ×
      (Fin (mR + nR₀ + 1) → ℝ) => -(a + p.1) :=
    (continuous_const.add continuous_fst).neg
  obtain ⟨τ, hτ, hτG⟩ : ∃ τ : e.Ω → WithTop ℝ≥0,
      IsStoppingTime e'.filtration τ ∧
        ∀ ω ∈ Gd, τ ω = hitBelow (fun t => -(a + e.W t ω)) (e.lifetime ω) 0 := by
    refine ⟨_, isStoppingTime_hitBelow_state hE'.2.1 hE'.2.2.1 hE'.2.2.2.1 hGd0
      (fun ω hω => by
        have hp := (hGdGood ω hω).isForcePath
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
      hitBelow (fun t => -(a + e'.W t ω)) (e'.lifetime ω) 0 :=
    hGd.mono fun ω hω _ => hτG ω hω
  let win := restartWindowOfAngleWord hκ hκ4 ρL₀ ρR₀ mL mR φ hφ
    xL xR a hy e' hE' τ hτ A hA hAζ hhit
  have ha : a < 0 := by linarith only [hy.2.1]
  have hzero := ae_zero_of_first_passage e' hE' ha hAζ hhit
  refine (hbound win).trans (measure_mono_ae (μ := e.P) ?_)
  filter_upwards [hGd, hzero] with ω hωG hz hωslow
  intro q hq1 hqζ
  change ((q : ℝ≥0) : ℝ≥0∞) < e.lifetime ω at hqζ
  change a + ((Prop59Stage.samp (e.W · ω) (fun i t => e.VL i t ω)
    (fun i t => e.VR i t ω) (e.lifetime ω)).2 q).1 < 7 / 4
  rw [Prop59Stage.samp_snd_of_lt _ _ _ hqζ]
  change a + e.W q ω < 7 / 4
  have hτeq := hτG ω hωG
  by_cases hωA : ω ∈ A
  · have hfin : (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) = τ ω :=
      coe_untopA_of_ne_top (ne_top_of_lt (hAζ ω hωA))
    have hqNN : (q : ℝ≥0) < 1 := by exact_mod_cast hq1
    have hbefore : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.lifetime ω →
        t < (τ ω).untopA → a + e.W t ω ≤ 0 := by
      intro t ht htt
      exact Prop59Stage.le_zero_of_lt_hitBelow
        (a := a) (w := fun u => e.W u ω) ht (by
        rw [← hτeq, ← hfin]
        exact_mod_cast htt)
    exact RootS5.RestartWindow.driver_lt_of_mem_slowEvent win a hωslow hbefore
      hz (fun hnA => False.elim (hnA hωA)) hqNN hqζ
  · have hle : (e.lifetime ω : WithTop ℝ≥0) ≤ τ ω := not_lt.1 hωA
    have hqt : ((q : ℝ≥0) : WithTop ℝ≥0) <
        hitBelow (fun t => -(a + e.W t ω)) (e.lifetime ω) 0 := by
      rw [← hτeq]
      exact lt_of_lt_of_le hqζ hle
    have hnonpos := Prop59Stage.le_zero_of_lt_hitBelow (a := a) hqζ hqt
    linarith only [hnonpos]

/-- The same probability constant applies when a buffer or localization
ends the observed word earlier. No trace over the full continuation
lifetime, or stopping-time property of the smaller lifetime, is used. -/
theorem exists_uniform_stopped_unit_bound {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL₀ nR₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ (mL mR : ℕ) (φ : ℕ → ℝ),
      (∀ i, φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) →
      ∀ (xL : Fin (mL + nL₀) → ℝ) (xR : Fin (mR + nR₀ + 1) → ℝ) (a : ℝ),
      (a, xL, xR) ∈ Prop59Stage.startsU →
      ∀ e : EvolutionData.{u} (mL + nL₀) (mR + nR₀ + 1),
      e.IsEvolution κ xL (angleWordL κ φ mL ρL₀) xR (angleWordR κ φ mR ρR₀) →
      ∀ L : e.Ω → ℝ≥0∞, (∀ᵐ ω ∂e.P, L ω ≤ e.lifetime ω) →
      ENNReal.ofReal p₀ ≤ e.P {ω |
        ((a, xL, xR), Prop59Stage.samp (e.W · ω) (fun i t => e.VL i t ω)
          (fun i t => e.VR i t ω) (L ω)) ∈ Prop59Stage.unitSet} := by
  obtain ⟨p₀, hp₀, hp₀1, hbound⟩ := exists_uniform_unit_bound.{u} hκ hκ4 ρL₀ ρR₀
  refine ⟨p₀, hp₀, hp₀1, ?_⟩
  intro mL mR φ hφ xL xR a hy e hE L hL
  refine (hbound mL mR φ hφ xL xR a hy e hE).trans (measure_mono_ae ?_)
  filter_upwards [hL] with ω hωL hω
  exact mem_unitSet_of_lifetime_le hωL hω

end InteractingSLE.Theorem14.GW2TipSystem.RootL6
