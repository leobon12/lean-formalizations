/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripExt
import InteractingSLE.Spec.Sec2.AddMarksGirsanov
import InteractingSLE.Spec.Zhan.TransienceTrace
import InteractingSLE.Spec.Sec7.ContinuityProb4Band
import InteractingSLE.Spec.Sec7.ContinuityProbCollision

/-!
# A.2, part 1: noncollision and the simple trace before the first force collision

Packet PROVE-ZHAN-A2P1. Source: Astra, *Follow-up proofs*, §A.2 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L524–L527): "The small curve is simple before its first force collision: after every positive own-time localization
all force gaps are positive, and bounded-drift absolute continuity transfers ordinary simplicity; the seed entrance
is handled by the finite-prefix continuity lemma in §B.1."

We work with an integrated `SLE_k(ρ)` evolution, `0 < k ≤ 4`, whose left word ends with a mark `x^{L,last} < 0`
carrying the only non-admissible weight: replacing that weight by another one (`ρL'`) gives a word with admissible
side partial sums, every proper left prefix and every right prefix sums to more than `−2`, and the total left weight is
at most `−2` (so the lifetime ends exactly when the driver meets the last left mark). Marks at the seed (`0⁻`, `0⁺`)
are allowed.

The proof is the source's bounded-drift absolute continuity, done with landed tools:

1. before the horizon `τ_n` (the first rational time at which the last left gap is at most `2δ_n`, capped by `n + 1`
   and the lifetime; `Sec7.Band.horizonL` for the one-mark family), the weight change `ρL → ρL'` only touches a mark at
   distance `≥ 2δ_n`, so Girsanov's theorem (`Sec2.IsSLEEvolutionUpTo.girsanov_changeWeights`) gives an equivalent
   measure `Q` under which the same processes are a local evolution of the admissible word before `τ_n`;
2. this local evolution is continued to an integrated one (`Sec5.Aux22Strip.exists_integrated_of_stop`) from the
   positive stop `T_n` (the hitting time of the level `4δ_n`, capped), at which the word is good;
3. for the admissible word, Remark 2.3 for `k ≤ 4` (`Zhan.IsIntegratedSLEEvolution.ae_simple_trace`, which handles the
   seed by the shrinking-prefix argument) gives noncollision at positive times and a simple trace in `ℍ`;
4. the conclusions hold before `τ_n` for the original processes, `Q`- hence `P`-almost surely, and `τ_n ↑ ζ`.

## Main results

* `ForceWord` threshold analysis of ordered states (`last_eq_of_thresholdCondition`);
* **`ae_noncollision_simpleTrace`**: almost surely `0 < ζ`, every force point is strictly separated from the driver at
  every positive time before `ζ`, and the canonical evaluation `t ↦ LP.traceAt t W` is a generating trace on every
  `[0, s]`, `s < ζ`, injective on `[0, ζ)`, lying in `ℍ` at positive times.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2P1

open QuantumZipper (H)
open Sec2 Sec7.Band Girsanov

/-! ### Colliding groups of an ordered state -/

section Groups

/-- A downward closed nonempty set of indices of `Fin n` is the initial segment up to its maximum. -/
theorem eq_Iic_max' {n : ℕ} {s : Finset (Fin n)} (hs : s.Nonempty)
    (hdown : ∀ i m, m ∈ s → i ≤ m → i ∈ s) : s = Finset.Iic (s.max' hs) := by
  ext i
  simp only [Finset.mem_Iic]
  exact ⟨fun hi => Finset.le_max' s i hi, fun hi => hdown i _ (Finset.max'_mem s hs) hi⟩

/-- **Left colliding group.** For an antitone left state `f ≤ w`, if the colliding left weights sum to at most `−2`
and every proper left prefix sums to more than `−2`, then the last left mark collides. -/
theorem last_eq_of_sum_le {j : ℕ} {f : Fin (j + 1) → ℝ} {w : ℝ} {ρ : Fin (j + 1) → ℝ} (hf : Antitone f)
    (hfw : ∀ i, f i ≤ w) (hpre : ∀ m : Fin (j + 1), m ≠ Fin.last j → -2 < ∑ i ∈ Finset.Iic m, ρ i)
    (hsum : (∑ i ∈ Finset.univ.filter (fun i => f i = w), ρ i) ≤ -2) : f (Fin.last j) = w := by
  by_contra hne
  set s := Finset.univ.filter (fun i => f i = w) with hs
  have hdown : ∀ i m, m ∈ s → i ≤ m → i ∈ s := fun i m hm him => by
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact le_antisymm (hfw i) (hm ▸ hf him)
  rcases s.eq_empty_or_nonempty with he | hne'
  · rw [he, Finset.sum_empty] at hsum
    linarith
  · have hm : s.max' hne' ≠ Fin.last j := fun h => by
      have := Finset.max'_mem s hne'
      rw [h] at this
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact hne this
    have := hpre _ hm
    rw [← eq_Iic_max' hne' hdown] at this
    linarith

/-- **Right colliding group.** For a monotone right state `w ≤ g`, if every right prefix sums to more than `−2`, the
colliding right weights sum to more than `−2`. -/
theorem neg_two_lt_sum_right {n : ℕ} {g : Fin n → ℝ} {w : ℝ} {ρ : Fin n → ℝ} (hg : Monotone g)
    (hwg : ∀ i, w ≤ g i) (hpre : ∀ m : Fin n, -2 < ∑ i ∈ Finset.Iic m, ρ i) :
    -2 < ∑ i ∈ Finset.univ.filter (fun i => g i = w), ρ i := by
  set s := Finset.univ.filter (fun i => g i = w) with hs
  have hdown : ∀ i m, m ∈ s → i ≤ m → i ∈ s := fun i m hm him => by
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact le_antisymm (hm ▸ hg him) (hwg i)
  rcases s.eq_empty_or_nonempty with he | hne'
  · rw [he, Finset.sum_empty]
    norm_num
  · rw [eq_Iic_max' hne' hdown]
    exact hpre _

/-- **The threshold of an ordered state is the collision of the last left mark** (under the prefix conditions). -/
theorem last_eq_of_thresholdCondition {j nR : ℕ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin nR → ℝ} {w : ℝ}
    {vL : Fin (j + 1) → ℝ} {vR : Fin nR → ℝ} (hL : Antitone vL) (hLw : ∀ i, vL i ≤ w) (hR : Monotone vR)
    (hRw : ∀ i, w ≤ vR i) (hpreL : ∀ m : Fin (j + 1), m ≠ Fin.last j → -2 < ∑ i ∈ Finset.Iic m, ρL i)
    (hpreR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.Iic m, ρR i)
    (h : ForceWord.ThresholdCondition ρL ρR w vL vR) : vL (Fin.last j) = w := by
  rcases h with h | h
  · exact last_eq_of_sum_le hL hLw hpreL h
  · exact absurd h (not_le.2 (neg_two_lt_sum_right hR hRw hpreR))

/-- **The threshold condition only sees the colliding marks.** If two left weight families agree except at marks
away from the driver, the threshold conditions agree. -/
theorem thresholdCondition_iff_of_eq {j nR : ℕ} {ρL ρL' : Fin (j + 1) → ℝ} {ρR : Fin nR → ℝ} {w : ℝ}
    {vL : Fin (j + 1) → ℝ} {vR : Fin nR → ℝ} (hρ : ∀ i, vL i = w → ρL' i = ρL i) :
    ForceWord.ThresholdCondition ρL' ρR w vL vR ↔ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  have e : (∑ i ∈ Finset.univ.filter (fun i => vL i = w), ρL' i) =
      ∑ i ∈ Finset.univ.filter (fun i => vL i = w), ρL i :=
    Finset.sum_congr rfl fun i hi => hρ i (Finset.mem_filter.1 hi).2
  unfold ForceWord.ThresholdCondition
  rw [e]

/-- The threshold condition is invariant under recentring at the driver. -/
theorem thresholdCondition_sub_iff {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ}
    {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} :
    ForceWord.ThresholdCondition ρL ρR 0 (fun i => vL i - w) (fun i => vR i - w) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  unfold ForceWord.ThresholdCondition
  simp only [sub_eq_zero]

end Groups

/-! ### Hitting times of a level by a gap -/

section Hit

variable {g : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- For a one-mark family, `LeftNear` is the gap condition. -/
theorem leftNear_one (c : ℝ) (w v : ℝ≥0 → ℝ) :
    LeftNear c w (fun _ : Fin 1 => v) = fun s => w s - v s ≤ c := by
  funext s
  simp only [LeftNear, exists_const]

/-- A gap that starts above `c` has a positive hitting time of `{g ≤ c}`. -/
theorem pos_hitTime (hg : ContinuousOn g {t | (t : ℝ≥0∞) < ζ}) (hζ : 0 < ζ) {c : ℝ} (hc : c < g 0) :
    0 < hitTime (fun s => g s ≤ c) ζ := by
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hca : ContinuousAt g 0 := hg.continuousAt (hopen.mem_nhds (by simpa using hζ))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hca.eventually (lt_mem_nhds hc))
  have hε' : (0 : ℝ≥0∞) < ((ε / 2).toNNReal : ℝ≥0∞) := by
    rw [ENNReal.coe_pos, Real.toNNReal_pos]; linarith
  refine lt_of_lt_of_le hε' (le_hitTime fun s hs _ => ?_)
  have hs' : (s : ℝ) < ε / 2 := by
    have := ENNReal.coe_lt_coe.1 hs
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by linarith)] at this
    exact this
  have hd : dist s 0 < ε := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg s.coe_nonneg]; linarith
  exact not_le.2 (hball hd)

/-- **Hitting a lower level takes strictly longer.** If `g 0 > c₂ > c₁` and `{g ≤ c₁}` is hit before `ζ`, then the
hitting time of `{g ≤ c₂}` is strictly smaller. -/
theorem hitTime_lt_hitTime (hg : ContinuousOn g {t | (t : ℝ≥0∞) < ζ}) {c₁ c₂ : ℝ} (hc : c₁ < c₂)
    (h0 : c₂ < g 0) (hfin : hitTime (fun s => g s ≤ c₁) ζ < ⊤) :
    hitTime (fun s => g s ≤ c₂) ζ < hitTime (fun s => g s ≤ c₁) ζ := by
  set u₁ := hitTime (fun s => g s ≤ c₁) ζ with hu₁
  obtain ⟨r, -, hrζ, hr⟩ := hitTime_lt_iff.1 hfin
  have hu₁r : u₁ ≤ (Real.toNNReal r : ℝ≥0) := hitTime_le hrζ hr
  have hu₁ζ : u₁ < ζ := lt_of_le_of_lt hu₁r hrζ
  set u : ℝ≥0 := u₁.toNNReal with hu
  have huu : (u : ℝ≥0∞) = u₁ := ENNReal.coe_toNNReal (ne_top_of_lt hfin)
  have huζ : (u : ℝ≥0∞) < ζ := by rw [huu]; exact hu₁ζ
  by_contra hle
  push Not at hle
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hca : ContinuousAt g u := hg.continuousAt (hopen.mem_nhds huζ)
  -- `g u ≥ c₂`: from the left (or `u = 0`)
  have hgu : c₂ ≤ g u := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h | h
    · rw [← h]; exact h0.le
    · have hne : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, h⟩
      refine ge_of_tendsto (hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio u))) ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hsu : (s : ℝ≥0∞) < u := ENNReal.coe_lt_coe.2 hs
      exact le_of_lt_hitTime hg (hsu.trans huζ) (lt_of_lt_of_le (hsu.trans_le huu.le) hle)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hca.eventually (lt_mem_nhds (hc.trans_le hgu)))
  have hε' : u₁ < ((u + (ε / 2).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [← huu, ENNReal.coe_lt_coe]
    exact lt_add_of_pos_right _ (Real.toNNReal_pos.2 (by linarith))
  refine absurd (le_hitTime (p := fun s => g s ≤ c₁) (ζ := ζ) fun s hs hsζ => ?_) (not_le.2 hε')
  rcases lt_or_ge s u with hsu | hsu
  · have hsu' : (s : ℝ≥0∞) < u := ENNReal.coe_lt_coe.2 hsu
    exact not_le.2 (hc.trans_le (le_of_lt_hitTime hg hsζ (lt_of_lt_of_le (hsu'.trans_le huu.le) hle)))
  · have hs' := ENNReal.coe_lt_coe.1 hs
    have hd : dist s u < ε := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hsu))]
      have : (s : ℝ) < u + ε / 2 := by
        have h2 := NNReal.coe_lt_coe.2 hs'
        rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at h2
        exact h2
      linarith
    exact not_le.2 (hball hd)

end Hit

/-! ### The path before its lifetime -/

section Path

variable {k : ℝ} {j nR : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (j + 1) → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (j + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

/-- **Before the lifetime the last left mark is strictly left of the driver** (the whole left side colliding would
be a threshold, the total left weight being at most `−2`). -/
theorem vL_last_lt (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) (hsum : ∑ i, ρL i ≤ -2)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vL (Fin.last j) t < w t := by
  have hfp := hp.isForcePath
  refine lt_of_le_of_ne (hfp.vL_le_w ht _) fun heq => hfp.not_threshold ht (Or.inl ?_)
  have hall : ∀ i, vL i t = w t := fun i =>
    le_antisymm (hfp.vL_le_w ht i) (heq ▸ hfp.antitone_vL ht (Fin.le_last i))
  have e : Finset.univ.filter (fun i => vL i t = w t) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => hall i
  show (∑ i ∈ Finset.univ.filter (fun i => vL i t = w t), ρL i) ≤ -2
  rw [e]
  exact hsum

/-- **The lifetime is positive**: the start is below threshold under the prefix conditions. -/
theorem lifetime_pos (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) (hF : IsOrderedForceWord xL xR)
    (hlast : xL (Fin.last j) < 0) (hpreL : ∀ m : Fin (j + 1), m ≠ Fin.last j → -2 < ∑ i ∈ Finset.Iic m, ρL i)
    (hpreR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.Iic m, ρR i) : 0 < ζ := by
  rcases eq_or_lt_of_le (bot_le : (⊥ : ℝ≥0∞) ≤ ζ) with h | h
  · exfalso
    have hthr := hp.isForcePath.threshold_of_eq_zero h.symm
    obtain ⟨hL, hL0, hR, hR0⟩ := hF
    have := last_eq_of_thresholdCondition hL hL0 hR hR0 hpreL hpreR hthr
    linarith
  · exact h

/-- **The last left gap reaches every positive level before a finite lifetime** (the threshold limit at `ζ` is the
collision of the last left mark). -/
theorem hitTime_gap_lt_lifetime (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
    (hpreL : ∀ m : Fin (j + 1), m ≠ Fin.last j → -2 < ∑ i ∈ Finset.Iic m, ρL i)
    (hpreR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.Iic m, ρR i)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin (j + 1) → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    (hζ0 : 0 < ζ) (hζ : ζ ≠ ⊤) {c : ℝ} (hc : 0 < c) :
    hitTime (fun s => w s - vL (Fin.last j) s ≤ c) ζ < ζ := by
  have hfp := hp.isForcePath
  set T : ℝ≥0 := ζ.toNNReal with hTdef
  have hTζ : (T : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζ
  have hT0 : 0 < T := by
    have : (0 : ℝ≥0∞) < (T : ℝ≥0∞) := by rw [hTζ]; exact hζ0
    exact_mod_cast this
  obtain ⟨w₀, vL₀, vR₀, hl, hthr⟩ := hlim T hT0 hTζ
  have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hTζ]; exact_mod_cast ht
  have hw₀ : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hl
  have hvL₀ : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp hl))
  have hvR₀ : ∀ i, Tendsto (fun t => vR i t) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp hl))
  have hL : Antitone vL₀ := fun i i' hii' =>
    le_of_tendsto_of_tendsto (hvL₀ i') (hvL₀ i) (hev.mono fun t ht => hfp.antitone_vL ht hii')
  have hLw : ∀ i, vL₀ i ≤ w₀ := fun i =>
    le_of_tendsto_of_tendsto (hvL₀ i) hw₀ (hev.mono fun t ht => hfp.vL_le_w ht i)
  have hR : Monotone vR₀ := fun i i' hii' =>
    le_of_tendsto_of_tendsto (hvR₀ i) (hvR₀ i') (hev.mono fun t ht => hfp.monotone_vR ht hii')
  have hRw : ∀ i, w₀ ≤ vR₀ i := fun i =>
    le_of_tendsto_of_tendsto hw₀ (hvR₀ i) (hev.mono fun t ht => hfp.w_le_vR ht i)
  have hlast := last_eq_of_thresholdCondition hL hLw hR hRw hpreL hpreR hthr
  have hgap : Tendsto (fun t => w t - vL (Fin.last j) t) (𝓝[<] T) (𝓝 0) := by
    have := hw₀.sub (hvL₀ (Fin.last j))
    rwa [hlast, sub_self] at this
  have hsmall : {t : ℝ≥0 | w t - vL (Fin.last j) t < c} ∈ 𝓝[<] T := hgap (gt_mem_nhds hc)
  obtain ⟨l, hlT, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT0).1 hsmall
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (l : ℝ) < T from hlT)
  have hq0 : (0 : ℝ) ≤ q := l.coe_nonneg.trans hq1.le
  have hqc : ((Real.toNNReal q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
  have hmem : Real.toNNReal q ∈ Ioo l T := ⟨by rw [← NNReal.coe_lt_coe, hqc]; exact hq1,
    by rw [← NNReal.coe_lt_coe, hqc]; exact hq2⟩
  have hqT : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < ζ := by rw [← hTζ]; exact_mod_cast hmem.2
  exact lt_of_le_of_lt (hitTime_le hqT (le_of_lt (hsub hmem))) hqT

/-- **The horizons exhaust the life**: every time before the lifetime is before some horizon `τ_n`. -/
theorem exists_lt_horizonL (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) (hsum : ∑ i, ρL i ≤ -2)
    (d : ℝ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∃ n : ℕ, (t : ℝ≥0∞) < horizonL (d / ((n : ℝ) + 1)) (n + 1) w (fun _ : Fin 1 => vL (Fin.last j)) ζ := by
  have hfp := hp.isForcePath
  obtain ⟨t', htt', ht'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt'' : t < t' := by exact_mod_cast htt'
  have hlt : ∀ s : ℝ≥0, s ≤ t' → (s : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht'ζ
  have hc : ContinuousOn (fun s => w s - vL (Fin.last j) s) (Icc 0 t') :=
    (hfp.continuousOn_w.sub (hfp.continuousOn_vL _)).mono fun s hs => hlt s hs.2
  obtain ⟨m, hm, hmle⟩ := Sec7.exists_pos_le_of_continuousOn_Icc hc fun s hs =>
    sub_pos.2 (vL_last_lt hp hsum (hlt s hs.2))
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * d / m) (t' : ℝ))
  have hn1 : 2 * d / m < (n : ℝ) + 1 := (le_max_left _ _).trans_lt (hn.trans (lt_add_one _))
  have hδ : 2 * (d / ((n : ℝ) + 1)) < m := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [mul_div_assoc', div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hm] at hn1
    linarith
  refine ⟨n, lt_min ?_ (lt_min ?_ ht)⟩
  · refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 htt'') (le_hitTime fun s hs hsζ => ?_)
    rw [leftNear_one]
    have hs' : s ≤ t' := (ENNReal.coe_lt_coe.1 hs).le
    exact not_le.2 (hδ.trans_le (hmle s ⟨zero_le, hs'⟩))
  · have : (t : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      exact (NNReal.coe_lt_coe.2 htt'').trans ((le_max_right _ _).trans_lt (hn.trans (lt_add_one _)))
    have h2 : t < ((n + 1 : ℕ) : ℝ≥0) := by exact_mod_cast this
    exact_mod_cast h2

end Path

/-! ### Small helpers -/

/-- A generating trace may be replaced by any function that agrees with it up to the horizon. -/
theorem isGeneratingTrace_congr {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η η' : ℝ≥0 → ℂ} (h : IsGeneratingTrace w T η)
    (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → η' t = η t) : IsGeneratingTrace w T η' := by
  refine ⟨by rw [heq 0 (by simp)]; exact h.1, h.2.1.congr fun t ht => heq t ht, fun t ht => ?_⟩
  have e : η' '' Icc 0 t = η '' Icc 0 t := image_congr fun r hr =>
    heq r ((ENNReal.coe_le_coe.2 hr.2).trans ht.le)
  rw [e]
  exact h.2.2 t ht

/-- A stopping time modified on a set that belongs to every σ-algebra of the filtration is a stopping time. -/
theorem isStoppingTime_ite {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓗 : Filtration ℝ≥0 mΩ} {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime 𝓗 S) {N : Set Ω} [DecidablePred (· ∈ N)]
    (hN : ∀ s, MeasurableSet[𝓗 s] N) (c : WithTop ℝ≥0) :
    IsStoppingTime 𝓗 fun ω => if ω ∈ N then c else S ω := by
  intro s
  have e : {ω | (if ω ∈ N then c else S ω) ≤ (s : WithTop ℝ≥0)} =
      (N ∩ {_ω | c ≤ (s : WithTop ℝ≥0)}) ∪ (Nᶜ ∩ {ω | S ω ≤ (s : WithTop ℝ≥0)}) := by
    ext ω
    by_cases hω : ω ∈ N <;> simp [hω]
  show MeasurableSet[𝓗 s] {ω | (if ω ∈ N then c else S ω) ≤ (s : WithTop ℝ≥0)}
  rw [e]
  exact ((hN s).inter (MeasurableSet.const _)).union ((hN s).compl.inter (hS s))

/-! ### The comparison before one horizon -/

section Evolution

variable {k : ℝ} {j nR : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin (j + 1) → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The `n`-th horizon: the first rational time at which the last left gap is at most `2d/(n + 1)`, capped by `n + 1`
and the lifetime. -/
def horizon (d : ℝ) (n : ℕ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    ℝ≥0∞ :=
  horizonL (d / ((n : ℝ) + 1)) (n + 1) (fun t => W t ω) (fun _ : Fin 1 => fun t => VL (Fin.last j) t ω) (ζ ω)

/-- **The comparison before the `n`-th horizon.** Almost surely there is an injective trace `η` in `ℍ` at positive
times such that, before the horizon `τ_n`, every force point is strictly separated from the driver at positive times
and `η` generates the chain of `W`. -/
theorem ae_lt_horizon (hk : 0 < k) (hk4 : k ≤ 4) (hF : IsOrderedForceWord xL xR) (hlast : xL (Fin.last j) < 0)
    (hρ' : ∀ i, i ≠ Fin.last j → ρL' i = ρL i) (hadm : Sec4.HasAdmissiblePartialSums k ρL' ρR xL xR)
    (hpreL : ∀ m : Fin (j + 1), m ≠ Fin.last j → -2 < ∑ i ∈ Finset.Iic m, ρL i)
    (hpreR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.Iic m, ρR i)
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (n : ℕ) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, Function.Injective η ∧ (∀ t : ℝ≥0, 0 < t → η t ∈ H) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < horizon (-xL (Fin.last j) / 8) n W VL ζ ω →
        (0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
          IsGeneratingTrace (fun s => W s ω) t η := by
  classical
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set d : ℝ := -xL (Fin.last j) / 8 with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set δ : ℝ := d / ((n : ℝ) + 1) with hδdef
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hδ : 0 < δ := div_pos hd0 (by linarith)
  have hδd : δ ≤ d := div_le_self hd0.le hn1
  have hg0 : 4 * δ < -xL (Fin.last j) := by rw [show -xL (Fin.last j) = 8 * d by rw [hd]; ring]; linarith
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set τ : Ω → ℝ≥0∞ := horizon d n W VL ζ with hτdef
  have hτst : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0) :=
    isStoppingTime_horizonL (VL := fun _ : Fin 1 => VL (Fin.last j)) hE𝓖.2.1 (fun _ => hE𝓖.2.2.1 _) δ (n + 1)
  have hgapτ : ∀ ω, IsIntegratedSLEPath k xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) → ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
        2 * δ ≤ W t ω - VL (Fin.last j) t ω := fun ω hp t ht =>
    le_gapL_of_lt_horizonL (vL := fun _ : Fin 1 => fun t => VL (Fin.last j) t ω) hp.isForcePath.continuousOn_w
      (fun _ => hp.isForcePath.continuousOn_vL _) ht 0
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR i ≠ ρR i → δ ≤ |W t ω - VR i t ω| := by
    filter_upwards [hE.2.2.2.2] with ω hp t ht
    refine ⟨fun i hi => ?_, fun i hi => absurd rfl hi⟩
    have hil : i = Fin.last j := by
      by_contra h
      exact hi (hρ' i h)
    subst hil
    have := hgapτ ω hp t ht
    rw [abs_of_nonneg (by linarith)]
    linarith
  obtain ⟨hQ, hE'⟩ := hE𝓖.isSLEEvolutionUpTo.girsanov_changeWeights hk ρL' ρR (fun s => hτst s)
    (fun ω => horizonL_le_lifetime _ _ _ _ _) (T := ((n + 1 : ℕ) : ℝ≥0))
    (fun ω => (natCast_le_coe (n + 1)) ▸ horizonL_le_n _ _ _ _ _) hδ hgap
  set Q := girsanovMeasure P 𝓖 B (weightDrift k δ ρL ρL' ρR ρR τ ζ W VL VR) (((n + 1 : ℕ) : ℝ≥0) + 1)
    with hQdef
  have : IsProbabilityMeasure Q := hQ.isProb
  -- the good paths
  have hgood0 : ∀ᵐ ω ∂P, IsIntegratedSLEPath k xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧
      ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∃ (w₀ : ℝ) (vL₀ : Fin (j + 1) → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
    filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hk] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood0)
  have hgoodN : ∀ ω, ω ∉ N → IsIntegratedSLEPath k xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧
      ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∃ (w₀ : ℝ) (vL₀ : Fin (j + 1) → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := fun ω hω => not_not.1 fun h => hω (hNsub h)
  have hNP : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  -- the continuation stop
  set cap : ℝ≥0 := (n : ℝ≥0) + 1 / 2 with hcap
  set T₀ : Ω → ℝ≥0∞ := fun ω =>
    min (hitTime (fun s => W s ω - VL (Fin.last j) s ω ≤ 4 * δ) (ζ ω)) (cap : ℝ≥0∞) with hT₀
  set T' : Ω → ℝ≥0∞ := fun ω => if ω ∈ N then ((1 / 2 : ℝ≥0) : ℝ≥0∞) else T₀ ω with hT'
  have hT'fin : ∀ ω, T' ω ≠ ⊤ := fun ω => by
    by_cases hω : ω ∈ N
    · simp only [hT', hω, ↓reduceIte]; exact ENNReal.coe_ne_top
    · simp only [hT', hω, ↓reduceIte]; exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  set T : Ω → ℝ≥0 := fun ω => (T' ω).toNNReal with hTdef
  have hTT' : ∀ ω, (T ω : ℝ≥0∞) = T' ω := fun ω => ENNReal.coe_toNNReal (hT'fin ω)
  have hT₀st : IsStoppingTime 𝓖 fun ω => (T₀ ω : WithTop ℝ≥0) := by
    have h1 := isStoppingTime_hitTime (𝓕 := 𝓖) (p := fun ω s => W s ω - VL (Fin.last j) s ω ≤ 4 * δ) (ζ := ζ)
      fun s => measurableSet_lt_and_le_of_adaptedBefore hE𝓖.2.1 (hE𝓖.2.2.1 _) s _
    exact h1.min (isStoppingTime_const 𝓖 cap)
  have hTst : IsStoppingTime (usualAugmentation 𝓖 Q) fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0) := by
    have hN𝓗 : ∀ s, MeasurableSet[usualAugmentation 𝓖 Q s] N := fun s =>
      Ito.measurableSet_usualAugmentation_of_null hNm (hQ.ac hN0) s
    have h := isStoppingTime_ite (fun s => Ito.le_usualAugmentation 𝓖 Q s _ (hT₀st s)) hN𝓗
      ((1 / 2 : ℝ≥0) : ℝ≥0∞)
    have e : (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => ((if ω ∈ N then ((1 / 2 : ℝ≥0) : ℝ≥0∞) else T₀ ω : ℝ≥0∞) : WithTop ℝ≥0) := by
      funext ω
      exact hTT' ω
    rw [e]
    exact h
  -- pathwise facts off `N`
  have hpos : ∀ ω, ω ∉ N → 0 < T₀ ω := fun ω hω => by
    obtain ⟨hp, -⟩ := hgoodN ω hω
    have hfp := hp.isForcePath
    have hζ0 := lifetime_pos hp hF hlast hpreL hpreR
    refine lt_min (pos_hitTime (hfp.continuousOn_w.sub (hfp.continuousOn_vL _)) hζ0 ?_) ?_
    · show 4 * δ < W 0 ω - VL (Fin.last j) 0 ω
      rw [hfp.w_zero, hfp.vL_zero]; linarith
    · rw [ENNReal.coe_pos, hcap]; positivity
  have hT0 : ∀ ω, 0 < T ω := fun ω => by
    rw [← ENNReal.coe_lt_coe, hTT', ENNReal.coe_zero]
    by_cases hω : ω ∈ N
    · simp only [hT', hω, ↓reduceIte, ENNReal.coe_pos]; norm_num
    · simp only [hT', hω, ↓reduceIte]; exact hpos ω hω
  have hTτP : ∀ ω, ω ∉ N → T₀ ω < τ ω := fun ω hω => by
    obtain ⟨hp, hlim⟩ := hgoodN ω hω
    have hfp := hp.isForcePath
    have hζ0 := lifetime_pos hp hF hlast hpreL hpreR
    have hgc : ContinuousOn (fun s => W s ω - VL (Fin.last j) s ω) {t | (t : ℝ≥0∞) < ζ ω} :=
      hfp.continuousOn_w.sub (hfp.continuousOn_vL _)
    have hg00 : 4 * δ < W 0 ω - VL (Fin.last j) 0 ω := by rw [hfp.w_zero, hfp.vL_zero]; linarith
    have hcapn : (cap : ℝ≥0∞) < ((n + 1 : ℕ) : ℝ≥0∞) := by
      rw [natCast_le_coe, ENNReal.coe_lt_coe, hcap, ← NNReal.coe_lt_coe]
      push_cast
      linarith
    refine lt_min ?_ (lt_min ((min_le_right _ _).trans_lt hcapn) ?_)
    · show T₀ ω < hitTime (LeftNear (2 * δ) (fun t => W t ω) (fun _ : Fin 1 => fun t => VL (Fin.last j) t ω))
        (ζ ω)
      rw [leftNear_one]
      by_cases hfin : hitTime (fun s => W s ω - VL (Fin.last j) s ω ≤ 2 * δ) (ζ ω) < ⊤
      · exact (min_le_left _ _).trans_lt (hitTime_lt_hitTime hgc (by linarith) hg00 hfin)
      · rw [not_lt, top_le_iff] at hfin
        rw [hfin]
        exact (min_le_right _ _).trans_lt ENNReal.coe_lt_top
    · by_cases hζ : ζ ω = ⊤
      · rw [hζ]; exact (min_le_right _ _).trans_lt ENNReal.coe_lt_top
      · exact (min_le_left _ _).trans_lt (hitTime_gap_lt_lifetime hp hpreL hpreR hlim hζ0 hζ (by linarith))
  have hTτ : ∀ᵐ ω ∂Q, (T ω : ℝ≥0∞) < τ ω := by
    refine hQ.ac.ae_le ?_
    filter_upwards [hNP] with ω hω
    rw [hTT']
    simp only [hT', hω, ↓reduceIte]
    exact hTτP ω hω
  have hgoodQ : ∀ᵐ ω ∂Q, Assembly2.GoodWord ρL' ρR (Assembly2.contWord W VL VR T ω) := by
    refine hQ.ac.ae_le ?_
    filter_upwards [hNP] with ω hω
    obtain ⟨hp, -⟩ := hgoodN ω hω
    have hfp := hp.isForcePath
    set t := T ω with ht
    have htτ : (t : ℝ≥0∞) < τ ω := by
      rw [ht, hTT']; simp only [hT', hω, ↓reduceIte]; exact hTτP ω hω
    have htζ : (t : ℝ≥0∞) < ζ ω := htτ.trans_le (horizonL_le_lifetime _ _ _ _ _)
    have ht0 : 0 < t := hT0 ω
    have hg2 := hgapτ ω hp t htτ
    refine ⟨fun i i' => sub_lt_sub_right (hp.vL_lt_vR htζ ht0 i i') _, ⟨fun i i' h =>
      sub_le_sub_right (hfp.antitone_vL htζ h) _, fun i => sub_nonpos.2 (hfp.vL_le_w htζ i), fun i i' h =>
      sub_le_sub_right (hfp.monotone_vR htζ h) _, fun i => sub_nonneg.2 (hfp.w_le_vR htζ i)⟩, fun hthr => ?_⟩
    have h1 : ForceWord.ThresholdCondition ρL' ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω) :=
      thresholdCondition_sub_iff.1 hthr
    have h2 := (thresholdCondition_iff_of_eq (ρL := ρL) fun i hi => by
      by_cases hil : i = Fin.last j
      · subst hil
        exfalso
        have : W t ω - VL (Fin.last j) t ω = 0 := by rw [hi, sub_self]
        linarith
      · exact hρ' i hil).1 h1
    exact hfp.not_threshold htζ h2
  obtain ⟨B', gW, gL, gR, ζG, hG, hag⟩ := Sec5.Aux22Strip.exists_integrated_of_stop hk hE' hTst hT0 hTτ hgoodQ
  have hsimple := Zhan.IsIntegratedSLEEvolution.ae_simple_trace hk hk4 hF hadm hG
  refine hQ.ac'.ae_le ?_
  filter_upwards [hag, hsimple] with ω ⟨_, _, hagω⟩ ⟨_, hsep, η, hη, hinj, hH, _⟩
  refine ⟨η, hinj, hH, fun t ht => ⟨fun ht0 => ?_, ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hagω t ht
    obtain ⟨hs1, hs2⟩ := hsep t ht0
    exact ⟨fun i => by rw [h2 i, h1]; exact hs1 i, fun i => by rw [h3 i, h1]; exact hs2 i⟩
  · exact Sec7.IsGeneratingTrace.congr_lt (hη.mono_horizon le_top) fun s hs =>
      (hagω s (lt_trans hs ht)).1

/-- **Noncollision and the simple trace before the first force collision** (A.2, L524–L527). For an integrated
`SLE_k(ρ)` evolution, `0 < k ≤ 4`, of an ordered word whose last left mark `x^{L,last} < 0` carries the only
non-admissible weight (`ρL'` agrees with `ρL` elsewhere and is admissible), with every proper left prefix and every
right prefix above `−2` and total left weight at most `−2`: almost surely `0 < ζ`; every force point is strictly
separated from the driver at every positive time before `ζ`; and `t ↦ LP.traceAt t W` is a generating trace on every
`[0, s]`, `s < ζ`, injective on `[0, ζ)`, in `ℍ` at positive times. -/
theorem ae_noncollision_simpleTrace (hk : 0 < k) (hk4 : k ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hlast : xL (Fin.last j) < 0) (hρ' : ∀ i, i ≠ Fin.last j → ρL' i = ρL i)
    (hadm : Sec4.HasAdmissiblePartialSums k ρL' ρR xL xR) (hsum : ∑ i, ρL i ≤ -2)
    (hpreL : ∀ m : Fin (j + 1), m ≠ Fin.last j → -2 < ∑ i ∈ Finset.Iic m, ρL i)
    (hpreR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.Iic m, ρR i)
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, 0 < ζ ω ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω →
        IsGeneratingTrace (fun t => W t ω) s (fun t => LP.traceAt t (fun r => W r ω))) ∧
      InjOn (fun t => LP.traceAt t (fun r => W r ω)) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → LP.traceAt t (fun r => W r ω) ∈ H := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ η : ℝ≥0 → ℂ, Function.Injective η ∧ (∀ t : ℝ≥0, 0 < t → η t ∈ H) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < horizon (-xL (Fin.last j) / 8) n W VL ζ ω →
        (0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω) ∧
          IsGeneratingTrace (fun s => W s ω) t η :=
    ae_all_iff.2 fun n => ae_lt_horizon hk hk4 hF hlast hρ' hadm hpreL hpreR hE n
  filter_upwards [hall, hE.2.2.2.2] with ω hn hp
  have hfp := hp.isForcePath
  set γ : ℝ≥0 → ℂ := fun t => LP.traceAt t (fun r => W r ω) with hγ
  -- around every time before `ζ`: a horizon beyond it, and `γ` equals that horizon's trace
  have key : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → ∃ η : ℝ≥0 → ℂ, Function.Injective η ∧
      (∀ t : ℝ≥0, 0 < t → η t ∈ H) ∧ IsGeneratingTrace (fun r => W r ω) s η ∧
      (0 < s → (∀ i, VL i s ω < W s ω) ∧ ∀ i, W s ω < VR i s ω) ∧ ∀ r : ℝ≥0, r ≤ s → γ r = η r := by
    intro s hs
    obtain ⟨s', hss', hs'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    obtain ⟨n, hnτ⟩ := exists_lt_horizonL hp hsum (-xL (Fin.last j) / 8) hs'ζ
    obtain ⟨η, hinj, hH, hτ⟩ := hn n
    have hs'n : (s' : ℝ≥0∞) < horizon (-xL (Fin.last j) / 8) n W VL ζ ω := hnτ
    have hsn : (s : ℝ≥0∞) < horizon (-xL (Fin.last j) / 8) n W VL ζ ω := hss'.trans hs'n
    have hgen' := (hτ s' hs'n).2
    refine ⟨η, hinj, hH, (hτ s hsn).2, (hτ s hsn).1, fun r hr => ?_⟩
    exact LP.traceAt_eq_of_isGeneratingTrace hgen' (hfp.continuousOn_w.mono fun t ht =>
      lt_trans (show (t : ℝ≥0∞) < s' from ht) hs'ζ) hfp.w_zero (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hss')
  refine ⟨lifetime_pos hp hF hlast hpreL hpreR, fun t ht0 ht => (key t ht).choose_spec.2.2.2.1 ht0,
    fun s hs => ?_, fun t₁ ht₁ t₂ ht₂ heq => ?_, fun t ht0 ht => ?_⟩
  · obtain ⟨η, -, -, hgen, -, hγη⟩ := key s hs
    exact isGeneratingTrace_congr hgen fun r hr => hγη r (ENNReal.coe_le_coe.1 hr)
  · have hmax : ((max t₁ t₂ : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      rcases le_total t₁ t₂ with h | h
      · rw [max_eq_right h]; exact ht₂
      · rw [max_eq_left h]; exact ht₁
    obtain ⟨η, hinj, -, -, -, hγη⟩ := key _ hmax
    refine hinj ?_
    rw [← hγη t₁ (le_max_left _ _), ← hγη t₂ (le_max_right _ _)]
    exact heq
  · obtain ⟨η, -, hH, -, -, hγη⟩ := key t ht
    have e : LP.traceAt t (fun r => W r ω) = η t := hγη t le_rfl
    rw [e]
    exact hH t ht0

end Evolution

end InteractingSLE.ZhanGT4.A2P1
