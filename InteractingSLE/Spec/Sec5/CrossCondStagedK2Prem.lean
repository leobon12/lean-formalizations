/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedK2Right
import InteractingSLE.Spec.Sec5.CrossCondStagedKillTrace
import InteractingSLE.Spec.Sec5.Prop59NodesFarPrem

/-!
# The killed comparison premises for evolutions traced up to the kill (ruling R78)

Packet PROVE-STAGED9. The experiment of Proposition 5.9 (PROVE-PROP59T2, re-proved by PROVE-PROP59-NODES for the
killed law) uses three comparison premises. R78 re-targets the per-candidate law to `IsStageLawFarK`, whose premise
class `CompPremiseFarK` contains every integrated evolution with a generating trace **up to its first far contact**
only. The three premises hold in that class:

* **unit** (`exists_compPremiseFarK_unit`): PROVE-PROP59T2's `exists_compPremise_unit` never uses its trace
  hypothesis; its proof, copied without that hypothesis, is `exists_compPremiseAll_unit` (every integrated evolution,
  traced or not), and the unit event is monotone under killing;
* **crossing** (`compPremiseFarK_crossL`, `compPremiseFarK_crossR`): the first far-left contact and the crossing of
  `−(2 + 1/8)` are trace-free (`ae_exists_isFirstFarContact_stage`: Aux. 22's swallow, `ae_swallow`); the far-right
  mark is not met before the crossing time, since its first contact `T` would be before the kill, so the trace would
  exist on `[0, T]`, which GB8's input 3 for traces up to the contact excludes
  (`StagedK2.ae_not_isGeneratingTrace_right_contact`).

Also `IsStageLawFarK.le_measure_imp` (the comparison form restricted to a start set, as `IsStageLawFar.le_measure`).
Nothing here uses Theorem 1.2, Theorem 1.3 or any result taking them as hypotheses (ruling R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedK2

open Prop59Stage Prop59Nodes Prop59Tips Supp8.GB8 StagedKill Coupling

/-! ### The unit premise over every evolution -/

/-- The comparison premise over **every** integrated evolution from a start in `D` (no trace hypothesis). -/
def CompPremiseAll (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (D : Set (Start nL nR))
    (S : Set (Start nL nR × Samp nL nR)) (p : ℝ≥0∞) : Prop :=
  ∀ y₀ ∈ D, ∀ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
    IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
    p ≤ P' {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')) ∈ S}

section Unit

variable {κ : ℝ} {nL₀ nR₀ : ℕ}

/-- **The uniform unit-time estimate of the even stages over every evolution** (Lemma 5.10 at the first passage
through `0`; PROVE-PROP59T2's `Prop59Stage.exists_compPremise_unit`, whose proof never uses the trace hypothesis —
copied here without it). -/
theorem exists_compPremiseAll_unit (hκ : 0 < κ) (hκ4 : κ < 4) (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ≥0∞, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ j : ℕ,
      CompPremiseAll κ (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) startsU unitSet p₀ := by
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

end Unit


/-- **The killed unit premise for evolutions traced up to the kill** (the unit event only constrains the samples
before the lifetime, so killing enlarges it; no trace is used). -/
theorem exists_compPremiseFarK_unit {κ : ℝ} {nL₀ nR₀ : ℕ} (hκ : 0 < κ) (hκ4 : κ < 4) (ρL₀ : Fin nL₀ → ℝ)
    (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ≥0∞, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ (j : ℕ) (iL : Fin (nL₀ + (j + 1))) (iR : Fin (nR₀ + (j + 1))),
      CompPremiseFarK κ (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) iL iR startsU unitSet p₀ := by
  obtain ⟨p₀, hp₀, hp₀1, hprem⟩ := exists_compPremiseAll_unit hκ hκ4 ρL₀ ρR₀
  refine ⟨p₀, hp₀, hp₀1, fun j iL iR y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE _ => ?_⟩
  refine (hprem j y₀ hy Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE).trans (measure_mono fun ω hω => ?_)
  intro q hq1 hqζ
  have hqζ' : ((q : ℝ≥0) : ℝ≥0∞) < ζ' ω := lt_of_lt_of_le hqζ farLife_le
  have h := hω q hq1 hqζ'
  change y₀.1 + ((samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω)).2 q).1 < 7 / 4 at h
  change y₀.1 + ((samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω)
    (farLife iL iR (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω))).2 q).1 < 7 / 4
  rw [samp_snd_of_lt_farLife hqζ]
  exact h

/-! ### The crossing premises -/

/-- **The first contact of a right coordinate** (deterministic): if a coordinate `v ≥ w` before `ζ` meets `w` at some
`u₀ < ζ`, it has a first meeting time `T ≤ u₀`, strictly right of `w` before it. -/
theorem exists_first_contact {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hvc : ContinuousOn v {s | (s : ℝ≥0∞) < ζ}) (hle : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → w s ≤ v s) {u₀ : ℝ≥0}
    (hu₀ζ : (u₀ : ℝ≥0∞) < ζ) (hu₀ : v u₀ ≤ w u₀) :
    ∃ T : ℝ≥0, T ≤ u₀ ∧ v T = w T ∧ ∀ s < T, w s < v s := by
  set g : ℝ≥0 → ℝ := fun s => v s - w s with hg
  have hIcc : Icc 0 u₀ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun s hs =>
    (ENNReal.coe_le_coe.2 hs.2).trans_lt hu₀ζ
  set K : Set ℝ≥0 := Icc 0 u₀ ∩ g ⁻¹' Iic 0 with hK
  have hKc : IsClosed K := ((hvc.sub hwc).mono hIcc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hu₀K : u₀ ∈ K := ⟨⟨zero_le, le_rfl⟩, by simp only [hg, mem_preimage, mem_Iic]; linarith⟩
  have hTK : sInf K ∈ K := hKc.csInf_mem ⟨u₀, hu₀K⟩ (OrderBot.bddBelow K)
  refine ⟨sInf K, hTK.1.2, ?_, fun s hs => ?_⟩
  · have h1 : g (sInf K) ≤ 0 := hTK.2
    have h2 := hle (sInf K) (hIcc hTK.1)
    simp only [hg] at h1
    linarith
  · by_contra h
    push Not at h
    have hsK : s ∈ K := ⟨⟨zero_le, hs.le.trans hTK.1.2⟩, by simp only [hg, mem_preimage, mem_Iic]; linarith⟩
    exact absurd (csInf_le (OrderBot.bddBelow K) hsK) (not_le.2 hs)

section Cross

variable {κ : ℝ} {j n : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The first far-left contact of a stage evolution, trace-free** (PROVE-PROP59T's `ae_stage_cross_left`, first
component, without its trace hypothesis: Aux. 22's swallow `ae_swallow` and GB8's `exists_isFirstFarContact` use no
trace). -/
theorem ae_exists_isFirstFarContact_stage (hκ : 0 < κ) (hκ4 : κ < 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hF : IsOrderedForceWord xL xR)
    (hxL : StrictAnti xL) (hxR : StrictMono xR) (hxm : xL (Fin.last j) < 0) (hw : IsStageWord κ ρL ρR) :
    ∀ᵐ ω ∂P, ∃ τ : ℝ≥0, IsFirstFarContact (fun t => W t ω) (fun t => VL (Fin.last j) t ω) (ζ ω) τ := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hj : 0 < j + 1 := Nat.succ_pos j
  have hlast := last_eq_mk j hj
  have hxm' : xL ⟨j + 1 - 1, Nat.sub_lt hj one_pos⟩ < 0 := by rw [hlast]; exact hxm
  have hpsL := neg_two_lt_partialL hκ hw
  have hpsR : ∀ k : Fin n, (k : ℕ) < n - 1 → -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ k), ρR l :=
    fun k _ => neg_two_lt_partialR hκ hw k
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ, ae_swallow hκ hκ4 hE hxL hxR hw]
    with ω hp hlim hsw
  have hinf : ζ ω = ⊤ → (∀ t : ℝ≥0, VL ⟨j + 1 - 1, Nat.sub_lt hj one_pos⟩ t ω < W t ω) → False := by
    intro hζ hlt
    rw [hlast] at hlt
    rcases hsw with hne | ⟨t, -, heq⟩
    · exact hne hζ
    · exact lt_irrefl _ (heq ▸ hlt t)
  obtain ⟨τ, hτ⟩ := exists_isFirstFarContact hκ hj hF hp hlim hxm' hw.2.2 hpsL hpsR hinf
  rw [hlast] at hτ
  exact ⟨τ, hτ⟩

end Cross

variable {κ : ℝ} {nL nR : ℕ}

/-- **The killed leftward crossing premise for evolutions traced up to the kill** (R78): every integrated evolution
of a stage word from an admissible start (`startsL`), with a generating trace up to its first far contact, killed
there, crosses the absolute level `−(2 + 1/8)` almost surely. -/
theorem compPremiseFarK_crossL (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hw : IsStageWordN κ ρL ρR) :
    CompPremiseFarK κ ρL ρR (farL hnL) (farR hnR) (startsL hnL hnR) (crossL (-(2 + 1 / 8)) (farL hnL)) 1 := by
  intro y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  obtain ⟨m, hm, hw'⟩ := hw
  subst hm
  have hw'' : IsStageWord κ ρL ρR := by
    have e : (fun i : Fin (m + 1) => ρL (Fin.cast rfl i)) = ρL := funext fun i => rfl
    rw [e] at hw'; exact hw'
  obtain ⟨hF, hxL, hxR, hfar, hxm, hxp⟩ := hy
  have hlast : farL hnL = Fin.last m := last_eq_mk m hnL
  rw [hlast] at hfar hxm
  have hpsR : ∀ k : Fin nR, (k : ℕ) < nR - 1 → -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ k), ρR l :=
    fun k _ => neg_two_lt_partialR hκ hw'' k
  have hNR := ae_not_isGeneratingTrace_right_contact hκ hκ4 hnR hF hxp hw''.2.2 hpsR hE
  refine one_le_measure_of_ae ?_
  filter_upwards [ae_exists_isFirstFarContact_stage hκ hκ4 hE hF hxL hxR hxm hw'', hNR, hE.2.2.2.2, htr]
    with ω hτω hNRω hp hηω
  obtain ⟨τ, hτ⟩ := hτω
  obtain ⟨η, hη⟩ := hηω
  have hfp := hp.isForcePath
  obtain ⟨t, htζ, hwt, hgap⟩ := exists_crossing_of_contact_level (ℓ := -(2 + 1 / 8) - y₀.1)
    hfp.continuousOn_w (fun s t hst ht => hfp.vL_le_of_le hst ht (Fin.last m)) (hfp.vL_zero (Fin.last m))
    (by linarith) hτ
  -- the far right mark is not met on `[0, t]`: its first contact would be before the kill
  have hright : ∀ u ≤ t, W' u ω < VR' (farR hnR) u ω := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u₀, hu₀t, hu₀⟩ := hcon
    have hu₀ζ : (u₀ : ℝ≥0∞) < ζ' ω := (ENNReal.coe_le_coe.2 hu₀t).trans_lt htζ
    obtain ⟨T, hTu, hmeet, hbefore⟩ := exists_first_contact hfp.continuousOn_w
      (hfp.continuousOn_vR (farR hnR)) (fun s hs => hfp.w_le_vR hs (farR hnR)) hu₀ζ hu₀
    have hTζ : (T : ℝ≥0∞) < ζ' ω := (ENNReal.coe_le_coe.2 hTu).trans_lt hu₀ζ
    have hTl : (T : ℝ≥0∞) ≤ farLife (farL hnL) (farR hnR) (W' · ω) (fun i t => VL' i t ω)
        (fun k t => VR' k t ω) (ζ' ω) := by
      refine le_min hTζ.le (le_farHit fun s hs => ?_)
      by_contra hsT
      push Not at hsT
      have hsT' : s < T := by exact_mod_cast hsT
      beta_reduce at hs
      rcases hs with h | h
      · rw [hlast] at h
        exact (hgap s (hsT'.le.trans (hTu.trans hu₀t))).ne' h
      · exact (hbefore s hsT').ne h
    exact hNRω T hTζ hbefore hmeet η (hη.mono_horizon hTl)
  show (y₀, samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω)
    (farLife (farL hnL) (farR hnR) (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω))) ∈ _
  rw [hlast]
  have hlt := lt_farLife_of (iL := Fin.last m) (iR := farR hnR) (w := fun t => W' t ω)
    (vL := fun i t => VL' i t ω) (vR := fun k t => VR' k t ω) hfp.continuousOn_w (hfp.continuousOn_vL _)
    (hfp.continuousOn_vR _) htζ fun u hu => ⟨hgap u hu, hright u hu⟩
  exact crossL_of_path (x := y₀.2) (continuousOn_lt_mono hfp.continuousOn_w farLife_le)
    (continuousOn_lt_mono (hfp.continuousOn_vL (Fin.last m)) farLife_le) hlt (by linarith) hgap

/-- **The killed rightward crossing premise for evolutions traced up to the kill** (by reflection). -/
theorem compPremiseFarK_crossR (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hw : IsStageWordN κ ρR ρL) :
    CompPremiseFarK κ ρL ρR (farL hnL) (farR hnR) (startsR hnL hnR) (crossR (2 + 1 / 8) (farR hnR)) 1 := by
  intro y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  obtain ⟨m, hm, hw'⟩ := hw
  subst hm
  have hw'' : IsStageWord κ ρR ρL := by
    have e : (fun i : Fin (m + 1) => ρR (Fin.cast rfl i)) = ρR := funext fun i => rfl
    rw [e] at hw'; exact hw'
  obtain ⟨hF, hxL, hxR, hfar, hxm, hxp⟩ := hy
  have hlast : farR hnR = Fin.last m := last_eq_mk m hnR
  rw [hlast] at hfar hxp
  have hEr := IsIntegratedSLEEvolution.reflect hE
  have hFr := Theorem14.CS3Cross.isOrderedForceWord_reflect hF
  have hxm' : (-y₀.2.2) (Fin.last m) < 0 := by simp only [Pi.neg_apply]; linarith
  have hxp' : 0 < (-y₀.2.1) ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ := by
    show 0 < -y₀.2.1 (farL hnL)
    linarith
  have hpsR : ∀ k : Fin nL, (k : ℕ) < nL - 1 → -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ k), ρL l :=
    fun k _ => neg_two_lt_partialR hκ hw'' k
  have hNL := ae_not_isGeneratingTrace_right_contact hκ hκ4 hnL hFr hxp' hw''.2.2 hpsR hEr
  refine one_le_measure_of_ae ?_
  filter_upwards [ae_exists_isFirstFarContact_stage hκ hκ4 hEr hFr (fun a b hab => neg_lt_neg (hxR hab))
    (fun a b hab => neg_lt_neg (hxL hab)) hxm' hw'', hNL, hEr.2.2.2.2, hE.2.2.2.2, htr]
    with ω hτω hNLω hpr hp hηω
  obtain ⟨τ, hτ⟩ := hτω
  obtain ⟨η, hη⟩ := hηω
  have hfr := hpr.isForcePath
  obtain ⟨t, htζ, hwt, hgap⟩ := exists_crossing_of_contact_level (ℓ := y₀.1 - (2 + 1 / 8))
    hfr.continuousOn_w (fun s t hst ht => hfr.vL_le_of_le hst ht (Fin.last m)) (hfr.vL_zero (Fin.last m))
    (by simp only [Pi.neg_apply]; linarith) hτ
  have hfp := hp.isForcePath
  have hgap' : ∀ u ≤ t, W' u ω < VR' (Fin.last m) u ω := fun u hu => by
    have := hgap u hu; simp only [Pi.neg_apply] at this; linarith
  -- the far left mark is not met on `[0, t]`: its first contact would be before the kill
  have hleft : ∀ u ≤ t, VL' (farL hnL) u ω < W' u ω := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u₀, hu₀t, hu₀⟩ := hcon
    have hu₀ζ : (u₀ : ℝ≥0∞) < ζ' ω := (ENNReal.coe_le_coe.2 hu₀t).trans_lt htζ
    obtain ⟨T, hTu, hmeet, hbefore⟩ := exists_first_contact hfr.continuousOn_w
      (hfr.continuousOn_vR ⟨nL - 1, Nat.sub_lt hnL one_pos⟩)
      (fun s hs => hfr.w_le_vR hs ⟨nL - 1, Nat.sub_lt hnL one_pos⟩) hu₀ζ
      (by show -VL' (farL hnL) u₀ ω ≤ -W' u₀ ω; linarith)
    have hTζ : (T : ℝ≥0∞) < ζ' ω := (ENNReal.coe_le_coe.2 hTu).trans_lt hu₀ζ
    have hTl : (T : ℝ≥0∞) ≤ farLife (farL hnL) (farR hnR) (W' · ω) (fun i t => VL' i t ω)
        (fun k t => VR' k t ω) (ζ' ω) := by
      refine le_min hTζ.le (le_farHit fun s hs => ?_)
      by_contra hsT
      push Not at hsT
      have hsT' : s < T := by exact_mod_cast hsT
      beta_reduce at hs
      rcases hs with h | h
      · have hb : -W' s ω < -VL' (farL hnL) s ω := hbefore s hsT'
        linarith
      · rw [hlast] at h
        exact (hgap' s (hsT'.le.trans (hTu.trans hu₀t))).ne h
    exact hNLω T hTζ hbefore hmeet _ (LP.isGeneratingTrace_reflect (hη.mono_horizon hTl))
  show (y₀, samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω)
    (farLife (farL hnL) (farR hnR) (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω))) ∈ _
  rw [hlast]
  have hlt := lt_farLife_of (iL := farL hnL) (iR := Fin.last m) (w := fun t => W' t ω)
    (vL := fun i t => VL' i t ω) (vR := fun k t => VR' k t ω) hfp.continuousOn_w (hfp.continuousOn_vL _)
    (hfp.continuousOn_vR _) htζ fun u hu => ⟨hleft u hu, hgap' u hu⟩
  refine crossR_of_path (x := y₀.2) (continuousOn_lt_mono hfp.continuousOn_w farLife_le)
    (continuousOn_lt_mono (hfp.continuousOn_vR (Fin.last m)) farLife_le) hlt ?_ hgap'
  simp only [Pi.neg_apply] at hwt; linarith

/-! ### The comparison form restricted to a start set -/

section Law

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R : Set Ω}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The comparison form of `IsStageLawFarK` restricted to a start set `D`** (as `IsStageLawFar.le_measure`). -/
theorem IsStageLawFarK.le_measure_imp (hL : IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ)
    {D : Set (Start nL nR)} (hD : MeasurableSet D) {S : Set (Start nL nR × Samp nL nR)} (hS : MeasurableSet S)
    {p : ℝ≥0∞} (hp1 : p ≤ 1) (hp : CompPremiseFarK κ ρL ρR iL iR D S p) {A : Set Ω} (hA : MeasurableSet[𝓠] A)
    (hAR : A ⊆ R) :
    p * P A ≤ P (A ∩ {ω | y ω ∈ D → (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := by
  have hS' : MeasurableSet ((Prod.fst ⁻¹' Dᶜ) ∪ S) := (measurable_fst hD.compl).union hS
  have h := hL.2 _ hS' p (fun y₀ _ Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr => by
    by_cases hy : y₀ ∈ D
    · refine (hp y₀ hy Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE htr).trans (measure_mono fun ω' hω' => ?_)
      exact Or.inr hω'
    · have : {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
          (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω'))) ∈
          (Prod.fst ⁻¹' Dᶜ) ∪ S} = univ := by
        ext ω'
        simp only [mem_union, mem_preimage, mem_compl_iff, hy, not_false_eq_true, true_or, mem_ofPred_eq,
          mem_univ]
      rw [this, measure_univ]
      exact hp1) A hA hAR
  refine h.trans (measure_mono fun ω hω => ⟨hω.1, fun hyD => ?_⟩)
  rcases hω.2 with h1 | h1
  · exact absurd hyD h1
  · exact h1

end Law

end InteractingSLE.Sec5.CrossCond.StagedK2
