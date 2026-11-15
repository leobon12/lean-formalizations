/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedKillLaw
import InteractingSLE.Spec.Sec5.Prop59NodesFarExp

/-! # R78: alternating experiments with traces only up to the far contact

The two localized GB8 crossing comparisons remain explicit. The unit estimate
uses no trace premise, and the remaining experiment argument is the landed one.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
namespace InteractingSLE.Wire.Late
open Coupling Sec5 Sec5.Prop59Stage Sec5.Prop59Nodes Sec5.Prop59Tips Sec5.CrossCond.StagedKill

def CompPremiseNoTrace (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (D : Set (Start nL nR))
    (S : Set (Start nL nR × Samp nL nR)) (p : ℝ≥0∞) : Prop :=
  ∀ y₀ ∈ D, ∀ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
    IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
    p ≤ P' {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')) ∈ S}


variable {κ : ℝ} {nL₀ nR₀ : ℕ}

theorem exists_compPremiseNoTrace_unit (hκ : 0 < κ) (hκ4 : κ < 4) (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ≥0∞, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ j : ℕ,
      CompPremiseNoTrace κ (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) startsU unitSet p₀ := by
  have hM2 := angleWeightBound_lt_two hκ
  obtain ⟨p₀, hp₀, hcross⟩ := crossing_lower_bound_restart_stoppingTime (C := stageDriftBound κ ρL₀ ρR₀) hκ
    (J := Icc (-angleWeightBound κ) (angleWeightBound κ)) isCompact_Icc
    (fun x hx => by simp only [mem_Ioi]; linarith [hx.1])
  refine ⟨ENNReal.ofReal (min p₀ 1), ENNReal.ofReal_pos.2 (lt_min hp₀ one_pos),
    ENNReal.ofReal_le_one.2 (min_le_right _ _), fun j => ?_⟩
  rintro ⟨a, xL, xR⟩ hy Ω' mΩ' P' _ 𝓕' W VL VR B ζ hE
  classical
  have ha0 : a < 0 := by have := hy.2.1; simp only at this; linarith
  set 𝓖 := usualAugmentation 𝓕' P' with h𝓖
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  -- the good samples
  set Good : Ω' → Prop := fun ω =>
    IsIntegratedSLEPath κ xL xR (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) (W · ω) (fun i t => VL i t ω)
      (fun k t => VR k t ω) (B · ω) (ζ ω) ∧
    ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∃ (w₀ : ℝ) (vL₀ : Fin (nL₀ + (j + 1)) → ℝ)
      (vR₀ : Fin (nR₀ + (j + 1)) → ℝ), Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) ∧ ForceWord.ThresholdCondition (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) w₀ vL₀ vR₀
    with hGood
  have hgood : ∀ᵐ ω ∂P', Good ω := by
    filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ] with ω h1 h2 using ⟨h1, h2⟩
  set Gd : Set Ω' := (toMeasurable P' {ω | ¬ Good ω})ᶜ with hGd
  have hGdm : MeasurableSet Gd := (measurableSet_toMeasurable _ _).compl
  have hnull : P' (toMeasurable P' {ω | ¬ Good ω}) = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hgood
  have hGdG : ∀ ω ∈ Gd, Good ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hGd𝓖 : MeasurableSet[𝓖 0] Gd :=
    (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕') (measurableSet_toMeasurable _ _) hnull 0).compl
  -- the first passage of the absolute driver above `0`
  have hΦ : Continuous fun p : ℝ × (Fin (nL₀ + (j + 1)) → ℝ) × (Fin (nR₀ + (j + 1)) → ℝ) => -(a + p.1) :=
    (continuous_const.add continuous_fst).neg
  obtain ⟨τ, hτ, hτG, hτnG⟩ : ∃ τ : Ω' → WithTop ℝ≥0, IsStoppingTime 𝓖 τ ∧
      (∀ ω ∈ Gd, τ ω = hitBelow (fun u => -(a + W u ω)) (ζ ω) 0) ∧ ∀ ω ∉ Gd, τ ω = ⊤ := by
    refine ⟨_, isStoppingTime_hitBelow_state hE𝓖.2.1 hE𝓖.2.2.1 hE𝓖.2.2.2.1 hGd𝓖
      (fun ω hω => by
        have hF := (hGdG ω hω).1.isForcePath
        exact hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
          (continuousOn_pi.2 hF.continuousOn_vR))) hΦ 0, fun ω hω => ?_, fun ω hω => ?_⟩
    · simp only [hω, ↓reduceIte]; rfl
    · simp only [hω, ↓reduceIte]
  have hζ𝓖 : IsStoppingTime 𝓖 fun ω => (ζ ω : WithTop ℝ≥0) := Ito.isStoppingTime_lifetime hE𝓖.2.1
  set A : Set Ω' := {ω | τ ω < (ζ ω : WithTop ℝ≥0)} with hAdef
  have hA : MeasurableSet[hτ.measurableSpace] A := by
    have h := (hζ𝓖.measurableSet_stopping_time_le hτ).compl
    have e : A = {ω | (ζ ω : WithTop ℝ≥0) ≤ τ ω}ᶜ := by
      ext ω
      show τ ω < (ζ ω : WithTop ℝ≥0) ↔ ¬ ((ζ ω : WithTop ℝ≥0) ≤ τ ω)
      exact not_le.symm
    rw [e]; exact h
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  have hAGd : ∀ ω ∈ A, ω ∈ Gd := fun ω hω => by
    by_contra h
    have : τ ω = ⊤ := hτnG ω h
    simp only [hAdef, mem_ofPred_eq, this] at hω
    exact not_top_lt hω
  -- at a sample of `A`, the hitting time is finite
  have hfin : ∀ ω ∈ A, hitBelow (fun u => -(a + W u ω)) (ζ ω) 0 = (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) := by
    intro ω hω
    have hne : τ ω ≠ ⊤ := ne_top_of_lt hω
    rw [coe_untopA_of_ne_top hne]
    exact (hτG ω (hAGd ω hω)).symm
  have hlife : ∀ ω ∈ A, ∀ t : ℝ≥0, (∀ u < t, |W ((τ ω).untopA + u) ω - W (τ ω).untopA ω| < 1) →
      (((τ ω).untopA + t : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    intro ω hω t hnear
    have hG := hGdG ω (hAGd ω hω)
    have hτ0 := eq_zero_of_hitBelow_eq hG.1.isForcePath.continuousOn_w hG.1.isForcePath.w_zero ha0 (hfin ω hω)
    exact lt_zeta_of_near hG.1 hy hκ hκ4 hG.2 hτ0 (lt_of_hitBelow_eq (hfin ω hω)) hnear
  have hρJ : stageρR κ ρR₀ (j + 1) 0 ∈ Icc (-angleWeightBound κ) (angleWeightBound κ) := by
    rw [stageρR_succ_zero]; exact newR_mem_Icc hκ hκ4 j
  have hmain := hcross P' 𝓖 (nR := nR₀ + j) xL xR (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) W VL VR B ζ τ hτ
    A hE𝓖 hρJ hA (fun ω hω => hω)
    (Eventually.of_forall fun ω hω t _ hnear => hlife ω hω t hnear)
    (Eventually.of_forall fun ω hω => Eventually.of_forall fun r _ hr1 hnear => by
      have hG := hGdG ω (hAGd ω hω)
      have hfp := hG.1.isForcePath
      set τ' := (τ ω).untopA
      have hτ0 := eq_zero_of_hitBelow_eq hfp.continuousOn_w hfp.w_zero ha0 (hfin ω hω)
      have hsζ := hlife ω hω r.toNNReal hnear
      have hws : |W (τ' + r.toNNReal) ω - W τ' ω| ≤ 1 := by
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r.toNNReal) with h0 | hpos
        · rw [← h0, add_zero, sub_self, abs_zero]; norm_num
        · have hc : ContinuousAt (fun u : ℝ≥0 => |W (τ' + u) ω - W τ' ω|) r.toNNReal := by
            have hcw : ContinuousAt (fun s => W s ω) (τ' + r.toNNReal) :=
              hfp.continuousOn_w.continuousAt ((isOpen_setOf_coe_lt _).mem_nhds hsζ)
            exact ((hcw.comp (continuous_const.add continuous_id).continuousAt).sub
              continuousAt_const).abs
          have hne : (𝓝[<] r.toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
          exact le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio r.toNNReal)))
            (eventually_nhdsWithin_of_forall (s := Iio r.toNNReal) fun u hu => (hnear u hu).le)
      have hg := gaps_of_near hG.1 hy hτ0 hsζ hws
      exact otherDrift_stage_le hκ hκ4 ρL₀ ρR₀ j (hfp.antitone_vL hsζ) (hfp.monotone_vR hsζ) hg.1 hg.2)
  -- the unit event contains the crossing event on `A` and the complement of `A` on good samples
  set X : Set Ω' := {ω | ∀ t : ℝ≥0, t < 1 → |W ((τ ω).untopA + t) ω - W (τ ω).untopA ω| < 1} with hXdef
  set U : Set Ω' := {ω | ((a, xL, xR), samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ unitSet}
    with hUdef
  have hsub : (A ∩ X) ∪ (Gd \ A) ⊆ U := by
    rintro ω (⟨hωA, hωX⟩ | ⟨hωG, hωA⟩)
    · intro q hq1 hqζ
      change ((q : ℝ≥0) : ℝ≥0∞) < ζ ω at hqζ
      have hG := hGdG ω (hAGd ω hωA)
      have hfp := hG.1.isForcePath
      set τ' := (τ ω).untopA
      have hτ0 := eq_zero_of_hitBelow_eq hfp.continuousOn_w hfp.w_zero ha0 (hfin ω hωA)
      show a + ((samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)).2 q).1 < 7 / 4
      rw [samp_snd_of_lt _ _ _ hqζ]
      by_cases hqτ : (q : ℝ≥0) < τ'
      · have := le_zero_of_lt_hitBelow (a := a) (w := fun u => W u ω) hqζ (by rw [hfin ω hωA]; exact_mod_cast hqτ)
        simp only at this ⊢; linarith
      · push Not at hqτ
        have hu : (q : ℝ≥0) - τ' < 1 := by
          have : ((q : ℝ≥0) : ℝ) < 1 := hq1
          rw [← NNReal.coe_lt_coe, NNReal.coe_sub hqτ, NNReal.coe_one]
          linarith [NNReal.coe_nonneg τ']
        have h1 := hωX _ hu
        rw [add_tsub_cancel_of_le hqτ, abs_lt] at h1
        simp only; linarith [h1.2]
    · intro q _ hqζ
      change ((q : ℝ≥0) : ℝ≥0∞) < ζ ω at hqζ
      have hG := hGdG ω hωG
      show a + ((samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)).2 q).1 < 7 / 4
      rw [samp_snd_of_lt _ _ _ hqζ]
      have hle : (ζ ω : WithTop ℝ≥0) ≤ τ ω := not_lt.1 hωA
      have hqτ : ((q : ℝ≥0) : WithTop ℝ≥0) < hitBelow (fun u => -(a + W u ω)) (ζ ω) 0 := by
        have h2 : τ ω = hitBelow (fun u => -(a + W u ω)) (ζ ω) 0 := hτG ω hωG
        rw [← h2]; exact lt_of_lt_of_le hqζ hle
      have := le_zero_of_lt_hitBelow (a := a) (w := fun u => W u ω) hqζ hqτ
      simp only at this ⊢; linarith
  -- the measure estimate
  have hdisj : Disjoint (A ∩ X) (Gd \ A) := Set.disjoint_left.2 fun ω h1 h2 => h2.2 h1.1
  have hGdA : MeasurableSet (Gd \ A) := hGdm.diff hAm
  have hcompl : P'.real Aᶜ ≤ P'.real (Gd \ A) := by
    have h1 : Aᶜ ⊆ (Gd \ A) ∪ Gdᶜ := fun ω hω => by
      by_cases hG : ω ∈ Gd
      · exact Or.inl ⟨hG, hω⟩
      · exact Or.inr hG
    have h2 : P'.real Gdᶜ = 0 := by
      rw [measureReal_def, hGd, compl_compl, hnull, ENNReal.toReal_zero]
    calc P'.real Aᶜ ≤ P'.real ((Gd \ A) ∪ Gdᶜ) := measureReal_mono h1
      _ ≤ P'.real (Gd \ A) + P'.real Gdᶜ := measureReal_union_le _ _
      _ = P'.real (Gd \ A) := by rw [h2, add_zero]
  have hsum : P'.real A + P'.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hAm, probReal_univ]
  have hreal : min p₀ 1 ≤ P'.real U := by
    have hm1 : min p₀ 1 ≤ p₀ := min_le_left _ _
    have hm2 : min p₀ 1 ≤ 1 := min_le_right _ _
    have hm0 : 0 ≤ min p₀ 1 := le_min hp₀.le zero_le_one
    have hAX := measureReal_union hdisj hGdA (μ := P')
    calc min p₀ 1 = min p₀ 1 * (P'.real A + P'.real Aᶜ) := by rw [hsum, mul_one]
      _ ≤ p₀ * P'.real A + P'.real Aᶜ := by
          nlinarith [measureReal_nonneg (μ := P') (s := A), measureReal_nonneg (μ := P') (s := Aᶜ)]
      _ ≤ P'.real (A ∩ X) + P'.real (Gd \ A) := add_le_add hmain hcompl
      _ = P'.real ((A ∩ X) ∪ (Gd \ A)) := hAX.symm
      _ ≤ P'.real U := measureReal_mono hsub
  calc ENNReal.ofReal (min p₀ 1) ≤ ENNReal.ofReal (P'.real U) := ENNReal.ofReal_le_ofReal hreal
    _ = P' U := ENNReal.ofReal_toReal (measure_ne_top _ _)


theorem exists_compPremiseFarK_unit {nL₀ nR₀ : ℕ} (hκ : 0 < κ) (hκ4 : κ < 4) (ρL₀ : Fin nL₀ → ℝ)
    (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ≥0∞, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ (j : ℕ) (iL : Fin (nL₀ + (j + 1))) (iR : Fin (nR₀ + (j + 1))),
      CompPremiseFarK κ (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) iL iR startsU unitSet p₀ := by
  obtain ⟨p₀, hp₀, hp₀1, hprem⟩ := exists_compPremiseNoTrace_unit hκ hκ4 ρL₀ ρR₀
  refine ⟨p₀, hp₀, hp₀1, fun j iL iR y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr => ?_⟩
  refine (hprem j y₀ hy Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE).trans (measure_mono fun ω hω => ?_)
  intro q hq1 hqζ
  have hqζ' : ((q : ℝ≥0) : ℝ≥0∞) < ζ' ω := lt_of_lt_of_le hqζ farLife_le
  have h := hω q hq1 hqζ'
  change y₀.1 + ((samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω)).2 q).1 < 7 / 4 at h
  change y₀.1 + ((samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω)
    (farLife iL iR (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω))).2 q).1 < 7 / 4
  rw [samp_snd_of_lt_farLife hqζ]
  exact h

end InteractingSLE.Wire.Late
