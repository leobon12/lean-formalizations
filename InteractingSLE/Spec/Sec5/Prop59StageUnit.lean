/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageDrift
import InteractingSLE.Spec.Coupling.AnnounceLifetime

/-!
# Proposition 5.9's even stages spend a unit of capacity with probability at least `p₀`

Packet PROVE-PROP59T2. Specification §5.2, proof of Proposition 5.9, p. 147:

> A successful even stage must pass through driver value zero before reaching its target band. […] Otherwise apply the
> crossing estimate at the first passage through zero. With conditional probability at least `p₀`, the
> constant-angle continuation stays in `[−1, 1]` for the next unit of capacity time. During such an interval it cannot
> complete the switch to `I₊`. […] The constant-angle evolution used for this comparison exists through the stopped
> unit interval: the other force points are separated and the first right weight is strictly larger than `−2`.

The even (rightward) stages are the depths `j + 1` with `j` even; this file proves the uniform estimate for **every**
evolution of the depth-`(j + 1)` word from an admissible start (`startsU`: absolute driver in `I₋ = (−9/4, −7/4)`,
every right mark other than the first at absolute position at least `7/4`). The sampled event `unitSet` says that the
absolute driver stays below `7/4` at the rational times before time `1` and the lifetime. The proof:

* the first passage `τ` of the absolute driver above `0` (`Coupling.hitBelow`) is a stopping time of the usual
  augmentation; at `τ` the absolute driver is `0`;
* after `τ`, while the driver stays within `1` of its value at `τ`, every left mark is at distance at least `3/4` (left
  marks start at most at the driver `≤ −7/4` and decrease) and so is every right mark other than the first; hence the
  lifetime is not reached (the threshold condition fails by Aux. lemma 3) and the remaining drift is bounded by the
  stage-independent `stageDriftBound` (`otherDrift_stage_le`);
* Lemma 5.10 at the stopping time `τ` (`Sec5.crossing_lower_bound_restart_stoppingTime`) gives `p₀`, depending only on
  `κ`, the drift bound and `J = [−M, M]`;
* on `{τ ≥ ζ}` the absolute driver stays `≤ 0`; on the crossing event it stays below `1` up to `τ + 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

open Coupling

/-! ### The unit event and the admissible starts -/

section Sets

variable {nL nR : ℕ}

/-- **The sampled unit event**: at every rational time before `1` and before the lifetime, the absolute driver is
below `7/4`. -/
def unitSet : Set (Start nL nR × Samp nL nR) :=
  {p | ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ) < 1 → ((q : ℝ≥0) : ℝ≥0∞) < p.2.1 → p.1.1 + (p.2.2 q).1 < 7 / 4}

theorem measurableSet_unitSet : MeasurableSet (unitSet (nL := nL) (nR := nR)) := by
  have e : (unitSet (nL := nL) (nR := nR)) = ⋂ q : ℚ≥0, {p : Start nL nR × Samp nL nR |
      ((q : ℝ≥0) : ℝ) < 1 → ((q : ℝ≥0) : ℝ≥0∞) < p.2.1 → p.1.1 + (p.2.2 q).1 < 7 / 4} := by
    ext p; simp only [unitSet, mem_ofPred_eq, mem_iInter]
  rw [e]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : ((q : ℝ≥0) : ℝ) < 1
  · simp only [hq, true_imp_iff]
    have h1 : MeasurableSet {p : Start nL nR × Samp nL nR | ((q : ℝ≥0) : ℝ≥0∞) < p.2.1} :=
      measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)
    have h2 : MeasurableSet {p : Start nL nR × Samp nL nR | p.1.1 + (p.2.2 q).1 < 7 / 4} :=
      measurableSet_lt ((measurable_fst.comp measurable_fst).add
        (measurable_fst.comp (measurable_sampAt q))) measurable_const
    have e2 : {p : Start nL nR × Samp nL nR | ((q : ℝ≥0) : ℝ≥0∞) < p.2.1 → p.1.1 + (p.2.2 q).1 < 7 / 4} =
        {p | ((q : ℝ≥0) : ℝ≥0∞) < p.2.1}ᶜ ∪ {p | p.1.1 + (p.2.2 q).1 < 7 / 4} := by
      ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff]; tauto
    rw [e2]
    exact h1.compl.union h2
  · simp only [hq, false_imp_iff, ofPred_true, MeasurableSet.univ]

/-- **The admissible starts of an even stage**: absolute driver in `I₋`, ordered force word, every right mark other
than the first at absolute position at least `7/4`. -/
def startsU : Set (Start nL nR) :=
  {y | -(9 / 4) < y.1 ∧ y.1 < -(7 / 4) ∧ IsOrderedForceWord y.2.1 y.2.2 ∧
    ∀ k : Fin nR, 0 < (k : ℕ) → 7 / 4 ≤ y.1 + y.2.2 k}

theorem measurableSet_startsU : MeasurableSet (startsU (nL := nL) (nR := nR)) := by
  have h1 : Measurable fun y : Start nL nR => (y.2.1, y.2.2) := measurable_snd
  have hV : Measurable fun y : Start nL nR => y.2.2 := measurable_snd.comp measurable_snd
  have h4 : MeasurableSet {y : Start nL nR | ∀ k : Fin nR, 0 < (k : ℕ) → 7 / 4 ≤ y.1 + y.2.2 k} := by
    rw [ofPred_forall]
    refine MeasurableSet.iInter fun k => ?_
    by_cases hk : 0 < (k : ℕ)
    · simp only [hk, true_imp_iff]
      exact measurableSet_le measurable_const (measurable_fst.add ((measurable_pi_apply k).comp hV))
    · simp only [hk, false_imp_iff, ofPred_true, MeasurableSet.univ]
  exact (measurableSet_lt measurable_const measurable_fst).inter ((measurableSet_lt measurable_fst
    measurable_const).inter ((h1 measurableSet_isOrderedForceWord).inter h4))

end Sets

/-! ### Pathwise facts at the first passage through `0` -/

section Path

variable {κ : ℝ} {nL₀ nR₀ : ℕ} {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ} {j : ℕ}
  {xL : Fin (nL₀ + (j + 1)) → ℝ} {xR : Fin (nR₀ + (j + 1)) → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin (nL₀ + (j + 1)) → ℝ≥0 → ℝ} {vR : Fin (nR₀ + (j + 1)) → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {a : ℝ}

/-- Before the first passage, the absolute driver is at most `0`. -/
theorem le_zero_of_lt_hitBelow {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ)
    (hlt : (s : WithTop ℝ≥0) < hitBelow (fun u => -(a + w u)) ζ 0) : a + w s ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have := hitBelow_le (f := fun u => -(a + w u)) (ε := 0) hs (by linarith)
  exact absurd hlt (not_lt.2 this)

/-- **At the first passage, the absolute driver is `0`**. -/
theorem eq_zero_of_hitBelow_eq (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (ha : a < 0)
    {τ : ℝ≥0} (hτ : hitBelow (fun u => -(a + w u)) ζ 0 = τ) : a + w τ = 0 := by
  have hf : ContinuousOn (fun u => -(a + w u)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := (continuousOn_const.add hw).neg
  have h1 : -(a + w τ) ≤ 0 := le_of_hitBelow_eq hf hτ
  have hτζ : (τ : ℝ≥0∞) < ζ := lt_of_hitBelow_eq hτ
  refine le_antisymm ?_ (by linarith)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ τ) with h0 | hpos
  · subst h0; rw [hw0]; linarith
  · by_contra hgt
    push Not at hgt
    have hc : ContinuousAt (fun u => a + w u) τ :=
      (continuousOn_const.add hw).continuousAt ((isOpen_setOf_coe_lt ζ).mem_nhds hτζ)
    have hev : ∀ᶠ u in 𝓝[<] τ, 0 < a + w u := (hc.eventually (lt_mem_nhds hgt)).filter_mono nhdsWithin_le_nhds
    have hne : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
    obtain ⟨u, hu, hut⟩ := (hev.and self_mem_nhdsWithin).exists
    have huζ : (u : ℝ≥0∞) < ζ := lt_trans (by exact_mod_cast hut) hτζ
    have hlt : (u : WithTop ℝ≥0) < hitBelow (fun u => -(a + w u)) ζ 0 := by
      rw [hτ]; exact_mod_cast hut
    linarith [le_zero_of_lt_hitBelow huζ hlt]

variable (hp : IsIntegratedSLEPath κ xL xR (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) w vL vR b ζ)
  (hy : (a, xL, xR) ∈ startsU)
include hp hy

/-- After the first passage, while the driver stays within `1` of its value there, every left mark and every right
mark other than the first is at distance at least `3/4`. -/
theorem gaps_of_near {τ : ℝ≥0} (hτ0 : a + w τ = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ)
    (hws : |w s - w τ| ≤ 1) :
    (∀ i, 3 / 4 ≤ w s - vL i s) ∧ ∀ k : Fin (nR₀ + j), 3 / 4 ≤ vR k.succ s - w s := by
  obtain ⟨ha1, ha2, hF, hR⟩ := hy
  have hfp := hp.isForcePath
  have hw1 : -1 ≤ a + w s ∧ a + w s ≤ 1 := by
    rw [abs_le] at hws; constructor <;> linarith [hws.1, hws.2]
  refine ⟨fun i => ?_, fun k => ?_⟩
  · have h1 : vL i s ≤ vL i 0 := hfp.vL_le_of_le zero_le hs i
    rw [hfp.vL_zero i] at h1
    have h2 : xL i ≤ 0 := hF.2.1 i
    simp only at ha2
    linarith [hw1.1]
  · have h1 : vR k.succ 0 ≤ vR k.succ s := hfp.le_vR_of_le zero_le hs k.succ
    rw [hfp.vR_zero k.succ] at h1
    have h2 := hR k.succ (by simp)
    simp only at h2
    linarith [hw1.2]

/-- **The lifetime is not reached while the driver stays within `1` of its value at the first passage** (the
threshold condition fails at every limit: left marks and the far right marks are at distance at least `3/4`, the
first right weight exceeds `−2`). -/
theorem lt_zeta_of_near (hκ : 0 < κ) (hκ4 : κ < 4)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin (nL₀ + (j + 1)) → ℝ)
      (vR₀ : Fin (nR₀ + (j + 1)) → ℝ), Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) ∧ ForceWord.ThresholdCondition (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) w₀ vL₀ vR₀)
    {τ : ℝ≥0} (hτ0 : a + w τ = 0) (hτζ : (τ : ℝ≥0∞) < ζ) {t : ℝ≥0} (hnear : ∀ u < t, |w (τ + u) - w τ| < 1) :
    ((τ + t : ℝ≥0) : ℝ≥0∞) < ζ := by
  by_contra hge
  push Not at hge
  have hζtop : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hge
  set T : ℝ≥0 := ζ.toNNReal with hT
  have hTζ : (T : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζtop
  have hτT : τ < T := by rw [← ENNReal.coe_lt_coe, hTζ]; exact hτζ
  have hTt : T ≤ τ + t := by rw [← ENNReal.coe_le_coe, hTζ]; exact hge
  obtain ⟨w₀, vL₀, vR₀, htend, hthr⟩ := hlim T (lt_of_le_of_lt zero_le hτT) hTζ
  have hev : ∀ᶠ u in 𝓝[<] T, τ < u ∧ u < T := by
    filter_upwards [Ioo_mem_nhdsLT hτT] with u hu using ⟨hu.1, hu.2⟩
  have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨τ, hτT⟩
  -- every state before `T` after `τ` has the gaps
  have hgap : ∀ u : ℝ≥0, τ < u → u < T →
      (∀ i, 3 / 4 ≤ w u - vL i u) ∧ (∀ k : Fin (nR₀ + j), 3 / 4 ≤ vR k.succ u - w u) ∧
        -1 ≤ a + w u ∧ a + w u ≤ 1 := by
    intro u hτu huT
    have huζ : (u : ℝ≥0∞) < ζ := by rw [← hTζ]; exact_mod_cast huT
    have hd : u - τ < t := by
      have : u < τ + t := lt_of_lt_of_le huT hTt
      exact (tsub_lt_iff_left hτu.le).2 this
    have h1 := hnear (u - τ) hd
    rw [add_tsub_cancel_of_le hτu.le] at h1
    have hg := gaps_of_near hp hy hτ0 huζ h1.le
    rw [abs_lt] at h1
    exact ⟨hg.1, hg.2, by linarith [h1.1], by linarith [h1.2]⟩
  have hw0 := (continuous_fst.tendsto _).comp htend
  have hvL0 : ∀ i, Tendsto (fun u => vL i u) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp htend))
  have hvR0 : ∀ k, Tendsto (fun u => vR k u) (𝓝[<] T) (𝓝 (vR₀ k)) := fun k =>
    ((continuous_apply k).tendsto _).comp ((continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp htend))
  have hL : ∀ i, 3 / 4 ≤ w₀ - vL₀ i := fun i =>
    ge_of_tendsto (hw0.sub (hvL0 i)) (hev.mono fun u hu => (hgap u hu.1 hu.2).1 i)
  have hR : ∀ k : Fin (nR₀ + j), 3 / 4 ≤ vR₀ k.succ - w₀ := fun k =>
    ge_of_tendsto ((hvR0 k.succ).sub hw0) (hev.mono fun u hu => (hgap u hu.1 hu.2).2.1 k)
  rcases hthr with hthrL | hthrR
  · have hempty : (Finset.univ.filter fun i => vL₀ i = w₀) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h; have := hL i; rw [h] at this; linarith
    rw [hempty, Finset.sum_empty] at hthrL
    linarith
  · have hsub : (Finset.univ.filter fun k => vR₀ k = w₀) ⊆ {0} := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases Fin.eq_zero_or_eq_succ k with h0 | ⟨k', rfl⟩
      · simp [h0]
      · have := hR k'; rw [hk] at this; linarith
    have hM := angleWeightBound_lt_two hκ
    have hsum : -2 < ∑ k ∈ Finset.univ.filter (fun k => vR₀ k = w₀), stageρR κ ρR₀ (j + 1) k := by
      rcases Finset.subset_singleton_iff.1 hsub with he | he
      · rw [he, Finset.sum_empty]; norm_num
      · rw [he, Finset.sum_singleton]
        have := (newR_mem_Icc hκ hκ4 j).1
        rw [show stageρR κ ρR₀ (j + 1) 0 = newR κ j from stageρR_succ_zero κ ρR₀ j]
        linarith
    linarith

end Path

/-! ### The unit premise -/

section Premise

variable {κ : ℝ} {nL₀ nR₀ : ℕ}

/-- **The uniform unit-time estimate of the even stages** (Lemma 5.10 at the first passage through `0`): there is
`p₀ ∈ (0, 1]`, depending only on `κ` and the initial word, such that at every depth `j + 1` every integrated evolution
of the stage word from an admissible start (`startsU`) keeps its absolute driver below `7/4` on the rational times
before `1` and the lifetime with probability at least `p₀`. -/
theorem exists_compPremise_unit (hκ : 0 < κ) (hκ4 : κ < 4) (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ≥0∞, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ j : ℕ,
      CompPremise κ (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) startsU unitSet p₀ := by
  have hM2 := angleWeightBound_lt_two hκ
  obtain ⟨p₀, hp₀, hcross⟩ := crossing_lower_bound_restart_stoppingTime (C := stageDriftBound κ ρL₀ ρR₀) hκ
    (J := Icc (-angleWeightBound κ) (angleWeightBound κ)) isCompact_Icc
    (fun x hx => by simp only [mem_Ioi]; linarith [hx.1])
  refine ⟨ENNReal.ofReal (min p₀ 1), ENNReal.ofReal_pos.2 (lt_min hp₀ one_pos),
    ENNReal.ofReal_le_one.2 (min_le_right _ _), fun j => ?_⟩
  rintro ⟨a, xL, xR⟩ hy Ω' mΩ' P' _ 𝓕' W VL VR B ζ hE _
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

end Premise

end Prop59Stage

end Sec5

end InteractingSLE
