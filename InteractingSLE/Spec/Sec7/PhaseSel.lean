/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux117
import InteractingSLE.Spec.Sec7.Aux104
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# §7.4, Aux. lemma 122: a seed entrance with opposite-sign seed parameters has no positive lifetime

Packet PROVE-STRIPSYS4. Specification §7.4.1, proof of Aux. lemma 122 (`source/spec/p385-432.md` L111–L139, p. 391):
"Suppose first `n > 0`. Then `a := r_L(n) + 2 > 0`, `b := r_R(n) + 2 < 0`. […] Before the first collision with a
distant mark, Aux. lemma 117 applies on an actual positive interval and gives the integrated driving equations,
including absolute reciprocal-gap integrability and no singular force push. The distant-force contribution to the
driver is bounded after the usual positive-gap localization. Aux. lemma 104 rules out such an entrance with (PS9.3).
If `n < 0`, the reflected inequalities `a < 0 < b` give the same contradiction. The argument may be made on countably
many time-zero events that bound the initial mark positions and weights and bound `min{|a|, |b|}` away from zero, and on
the positive-gap localizations which exhaust their available initial intervals. Hence the contradiction applies also
to random initial words."

The word has `nL + 1` left and `nR + 1` right marks; index `0` is the seed (`0⁻`, `0⁺`), the other marks are
distant: their (random, possibly `ω`-dependent) initial positions are strictly separated from `0`.

## Main definitions

* `distDrift ρL ρR w vL vR t`: the drift of the distant marks,
  `∑_{i ≠ 0} ρ^L_i/(w − v^L_i) + ∑_{j ≠ 0} ρ^R_j/(w − v^R_j)`;
* `DistNear δ w vL vR s`: some distant mark is within `δ` of the driver at time `s`;
* `gapLoc δ w vL vR T`: the positive-gap localization, the first rational time before `T` at which a distant mark is
  within `δ` of the driver, capped by `T`.

## Main results

* `isSeedEntrance_of_isWordEntrance` (pathwise): before a time at which all distant gaps are `≥ δ`, the
  seed pair satisfies the hypotheses of Aux. lemma 104 with the distant drift as its bounded extra drift;
* **`ae_lifetime_eq_zero_of_isWordEntrance`**: if the integrated equations of the word hold on `[0, T)` with an
  `𝓕`-Brownian motion and the seed parameters `a = ρ^L_0 + 2`, `b = ρ^R_0 + 2` have opposite signs, then `T = 0` almost
  surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSel

open Aux117 MartChar

/-! ### The distant drift -/

section Drift

variable {nL nR : ℕ}

/-- The drift contributed by the distant marks (all marks except the seeds, index `0`). -/
def distDrift (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ)
    (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (∑ i : Fin nL, ρL i.succ / (w t - vL i.succ t)) + ∑ j : Fin nR, ρR j.succ / (w t - vR j.succ t)

/-- Some distant mark is within `δ` of the driver at time `s`. -/
def DistNear (δ : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ≥0) :
    Prop :=
  (∃ i : Fin nL, w s - vL i.succ s ≤ δ) ∨ ∃ j : Fin nR, vR j.succ s - w s ≤ δ

/-- The bound of the distant drift when every distant gap is at least `δ`. -/
def driftBound (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (δ : ℝ) : ℝ :=
  ((∑ i : Fin nL, |ρL i.succ|) + ∑ j : Fin nR, |ρR j.succ|) / δ

theorem abs_div_le_of_le {ρ g δ : ℝ} (hδ : 0 < δ) (hg : δ ≤ |g|) : |ρ / g| ≤ |ρ| / δ := by
  rw [abs_div]
  exact div_le_div_of_nonneg_left (abs_nonneg ρ) hδ hg

theorem abs_distDrift_le {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {δ : ℝ} (hδ : 0 < δ) {t : ℝ≥0}
    (hL : ∀ i : Fin nL, δ ≤ w t - vL i.succ t) (hR : ∀ j : Fin nR, δ ≤ vR j.succ t - w t) :
    |distDrift ρL ρR w vL vR t| ≤ driftBound ρL ρR δ := by
  unfold distDrift driftBound
  rw [add_div, Finset.sum_div, Finset.sum_div]
  refine (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)) ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)))
  · exact abs_div_le_of_le hδ ((hL i).trans (le_abs_self _))
  · refine abs_div_le_of_le hδ ((hR j).trans ?_)
    rw [abs_sub_comm]
    exact le_abs_self _

end Drift

/-! ### The pathwise reduction to Aux. lemma 104 -/

section Path

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w b : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {T T' : ℝ≥0∞}

theorem intervalIntegrable_div {f : ℝ → ℝ} {t : ℝ} (ρ : ℝ) (hf : IntervalIntegrable (fun s => (f s)⁻¹) volume 0 t) :
    IntervalIntegrable (fun s => ρ / f s) volume 0 t := by
  simpa only [div_eq_mul_inv] using hf.const_mul ρ

/-- **The seed pair of a word satisfies the hypotheses of Aux. lemma 104** before any time `T' ≤ T` before which every
distant gap is at least `δ > 0`, with the distant drift as the extra drift and `driftBound ρL ρR δ` as its bound. -/
theorem isSeedEntrance_of_isWordEntrance (h : IsWordEntrance κ xL xR ρL ρR w vL vR b T)
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hTT : T' ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' →
      (∀ i : Fin nL, δ ≤ w t - vL i.succ t) ∧ ∀ j : Fin nR, δ ≤ vR j.succ t - w t) :
    Aux104.IsSeedEntrance κ (ρL 0) (ρR 0) (driftBound ρL ρR δ) w (vL 0) (vR 0) b (distDrift ρL ρR w vL vR) T' := by
  have hT : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' → (t : ℝ≥0∞) < T := fun t ht => lt_of_lt_of_le ht hTT
  have hiL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' → ∀ i, IntervalIntegrable
      (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := fun t ht i =>
    intervalIntegrable_div (ρL i) (h.integrable_gapL t (hT t ht) i)
  have hiR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' → ∀ j, IntervalIntegrable
      (fun s : ℝ => ρR j / (w s.toNNReal - vR j s.toNNReal)) volume 0 t := fun t ht j =>
    intervalIntegrable_div (ρR j) (h.integrable_gapR t (hT t ht) j)
  have hie : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' →
      IntervalIntegrable (fun s : ℝ => distDrift ρL ρR w vL vR s.toNNReal) volume 0 t := by
    intro t ht
    unfold distDrift
    exact (MartChar.intervalIntegrable_fun_sum fun (i : Fin nL) => hiL t ht i.succ).add
      (MartChar.intervalIntegrable_fun_sum fun (j : Fin nR) => hiR t ht j.succ)
  refine ⟨fun t ht => h.vL_le_w t (hT t ht) 0, fun t ht => h.w_le_vR t (hT t ht) 0,
    fun t ht => h.integrable_gapL t (hT t ht) 0, fun t ht => ?_, hie,
    fun t ht => abs_distDrift_le hδ (hgap t ht).1 (hgap t ht).2, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    measure_mono_null ?_ (h.volume_collisionL 0), measure_mono_null ?_ (h.volume_collisionR 0)⟩
  · have e : (fun s : ℝ => (vR 0 s.toNNReal - w s.toNNReal)⁻¹) =
        fun s => -(w s.toNNReal - vR 0 s.toNNReal)⁻¹ := by
      funext s
      rw [← inv_neg, neg_sub]
    rw [e]
    exact (h.integrable_gapR t (hT t ht) 0).neg
  · rw [h.w_eq t (hT t ht), Fin.sum_univ_succ, Fin.sum_univ_succ, intervalIntegral.integral_add
      (((hiL t ht 0).add (hiR t ht 0))) (hie t ht), intervalIntegral.integral_add (hiL t ht 0) (hiR t ht 0)]
    unfold distDrift
    rw [intervalIntegral.integral_add
      (MartChar.intervalIntegrable_fun_sum fun (i : Fin nL) => hiL t ht i.succ)
      (MartChar.intervalIntegrable_fun_sum fun (j : Fin nR) => hiR t ht j.succ),
      intervalIntegral.integral_finsetSum fun i _ => hiL t ht i.succ,
      intervalIntegral.integral_finsetSum fun j _ => hiR t ht j.succ]
    ring
  · rw [h.vL_eq t (hT t ht) 0, hxL, zero_add]
  · rw [h.vR_eq t (hT t ht) 0, hxR, zero_add]
  · exact fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2.1 hTT, hs.2.2⟩
  · exact fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2.1 hTT, hs.2.2⟩

end Path

/-! ### The positive-gap localization -/

section Loc

variable {nL nR : ℕ}

/-- **The positive-gap localization**: the first rational time before `T` at which a distant mark is within `δ` of
the driver, capped by `T`. -/
def gapLoc (δ : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (T : ℝ≥0∞) :
    ℝ≥0∞ :=
  min T (Band.hitTime (DistNear δ w vL vR) T)

variable {δ : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {T : ℝ≥0∞}

theorem gapLoc_le : gapLoc δ w vL vR T ≤ T := min_le_left _ _

/-- **Before the localization every distant gap is at least `δ`.** -/
theorem le_gap_of_lt_gapLoc (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < T}) (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < T})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < gapLoc δ w vL vR T) :
    (∀ i : Fin nL, δ ≤ w t - vL i.succ t) ∧ ∀ j : Fin nR, δ ≤ vR j.succ t - w t := by
  have htT : (t : ℝ≥0∞) < T := lt_of_lt_of_le ht (min_le_left _ _)
  have htH : (t : ℝ≥0∞) < Band.hitTime (DistNear δ w vL vR) T := lt_of_lt_of_le ht (min_le_right _ _)
  refine ⟨fun i => ?_, fun j => ?_⟩
  · refine Band.le_of_lt_hitTime (g := fun s => w s - vL i.succ s) (hw.sub (hvL i.succ)) htT
      (lt_of_lt_of_le htH (Band.hitTime_mono fun s hs => Or.inl ⟨i, hs⟩))
  · refine Band.le_of_lt_hitTime (g := fun s => vR j.succ s - w s) ((hvR j.succ).sub hw) htT
      (lt_of_lt_of_le htH (Band.hitTime_mono fun s hs => Or.inr ⟨j, hs⟩))

/-- **The localization is positive** when `T > 0` and every distant gap exceeds `δ` at time `0`. -/
theorem gapLoc_pos (hT : 0 < T) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < T}) (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < T})
    (hL : ∀ i : Fin nL, δ < w 0 - vL i.succ 0) (hR : ∀ j : Fin nR, δ < vR j.succ 0 - w 0) :
    0 < gapLoc δ w vL vR T := by
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < T} := isOpen_lt ENNReal.continuous_coe continuous_const
  have h0 : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < T} := by simpa using hT
  have hnhds : {t : ℝ≥0 | (t : ℝ≥0∞) < T} ∈ 𝓝 (0 : ℝ≥0) := hopen.mem_nhds h0
  have hevL : ∀ᶠ s in 𝓝 (0 : ℝ≥0), ∀ i : Fin nL, δ < w s - vL i.succ s :=
    Filter.eventually_all.2 fun i =>
      ((hw.sub (hvL i.succ)).continuousAt hnhds).eventually (lt_mem_nhds (hL i))
  have hevR : ∀ᶠ s in 𝓝 (0 : ℝ≥0), ∀ j : Fin nR, δ < vR j.succ s - w s :=
    Filter.eventually_all.2 fun j =>
      (((hvR j.succ).sub hw).continuousAt hnhds).eventually (lt_mem_nhds (hR j))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hevL.and hevR)
  have hH : ENNReal.ofReal ε ≤ Band.hitTime (DistNear δ w vL vR) T := by
    refine Band.le_hitTime fun s hs _ hnear => ?_
    have hsε : (s : ℝ) < ε := by
      have := (ENNReal.ofReal_lt_ofReal_iff hε).1 (by rwa [ENNReal.ofReal_coe_nnreal])
      exact this
    have hd : dist s 0 < ε := by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, NNReal.abs_eq]
      exact hsε
    obtain ⟨h1, h2⟩ := hball hd
    rcases hnear with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact absurd hi (not_le.2 (h1 i))
    · exact absurd hj (not_le.2 (h2 j))
  exact lt_min hT (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) hH)

end Loc

/-! ### Aux. lemma 104 for a word with distant marks -/

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL nR : ℕ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W B : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}

/-- **The localization is a stopping time** of every right-continuous filtration containing `𝓕`. -/
theorem isStoppingTime_gapLoc {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] (h𝓕𝓖 : 𝓕 ≤ 𝓖)
    (hW : AdaptedBefore 𝓕 T W) (hVL : ∀ i, AdaptedBefore 𝓕 T (VL i)) (hVR : ∀ j, AdaptedBefore 𝓕 T (VR j))
    (δ : ℝ) :
    IsStoppingTime 𝓖 fun ω => (gapLoc δ (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (T ω) :
      WithTop ℝ≥0) := by
  have h1 : IsStoppingTime 𝓖 fun ω => (T ω : WithTop ℝ≥0) := fun i =>
    h𝓕𝓖 i _ (Aux104.isStoppingTime_lifetime hW i)
  have h2 : IsStoppingTime 𝓖 fun ω => (Band.hitTime (DistNear δ (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω)) (T ω) : WithTop ℝ≥0) := by
    refine Band.isStoppingTime_hitTime fun s => h𝓕𝓖 s _ ?_
    have e : {ω | (s : ℝ≥0∞) < T ω ∧ DistNear δ (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s} =
        {ω | (s : ℝ≥0∞) < T ω} ∩ ((⋃ i : Fin nL, {ω | Girsanov.killed T W s ω -
          Girsanov.killed T (VL i.succ) s ω ≤ δ}) ∪ ⋃ j : Fin nR, {ω | Girsanov.killed T (VR j.succ) s ω -
            Girsanov.killed T W s ω ≤ δ}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_union, mem_iUnion, DistNear]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        simpa only [Girsanov.killed_of_lt h1] using h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        simpa only [Girsanov.killed_of_lt h1] using h2
    rw [e]
    have hT : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < T ω} := by simpa using hW s univ MeasurableSet.univ
    refine hT.inter (MeasurableSet.union (MeasurableSet.iUnion fun i => ?_) (MeasurableSet.iUnion fun j => ?_))
    · exact ((Girsanov.measurable_killed hW s).sub (Girsanov.measurable_killed (hVL i.succ) s)) measurableSet_Iic
    · exact ((Girsanov.measurable_killed (hVR j.succ) s).sub (Girsanov.measurable_killed hW s)) measurableSet_Iic
  exact h1.min h2

/-- Adaptedness before `T` passes to the localization, in a right-continuous filtration containing `𝓕`. -/
theorem adaptedBefore_gapLoc {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] (h𝓕𝓖 : 𝓕 ≤ 𝓖)
    (hW : AdaptedBefore 𝓕 T W) (hVL : ∀ i, AdaptedBefore 𝓕 T (VL i)) (hVR : ∀ j, AdaptedBefore 𝓕 T (VR j))
    (δ : ℝ) {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 T X) :
    AdaptedBefore 𝓖 (fun ω => gapLoc δ (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (T ω)) X := by
  have hX𝓖 : AdaptedBefore 𝓖 T X := fun t A hA => h𝓕𝓖 t _ (hX t A hA)
  exact AdaptedBefore.of_le hX𝓖 (fun s => isStoppingTime_gapLoc h𝓕𝓖 hW hVL hVR δ s) fun ω => gapLoc_le

/-- **Aux. lemma 104 with distant marks** (the contradiction step of Aux. lemma 122, p. 391). Let `B` be an
`𝓕`-Brownian motion and let the driver and the marks of a word with `nL + 1` left and `nR + 1` right marks be adapted
before `T` and satisfy, almost surely, the integrated equations on `[0, T)` (`IsWordEntrance`), with both seeds
(index `0`) at `0` and every other mark strictly separated from `0` (its initial position may depend on `ω`). If the
seed parameters `a = ρ^L_0 + 2` and `b = ρ^R_0 + 2` have opposite signs, then `T = 0` almost surely. -/
theorem ae_lifetime_eq_zero_of_isWordEntrance {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hW : AdaptedBefore 𝓕 T W)
    (hVL : ∀ i, AdaptedBefore 𝓕 T (VL i)) (hVR : ∀ j, AdaptedBefore 𝓕 T (VR j))
    (hab : (0 < ρL 0 + 2 ∧ ρR 0 + 2 < 0) ∨ (0 < ρR 0 + 2 ∧ ρL 0 + 2 < 0))
    (hpath : ∀ᵐ ω ∂P, IsWordEntrance κ (xL ω) (xR ω) ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (B · ω) (T ω))
    (hseed : ∀ᵐ ω ∂P, xL ω 0 = 0 ∧ xR ω 0 = 0 ∧ (∀ i : Fin nL, xL ω i.succ < 0) ∧ ∀ j : Fin nR, 0 < xR ω j.succ) :
    ∀ᵐ ω ∂P, T ω = 0 := by
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hB𝓖 := Ito.isFilteredBrownianReal_usualAugmentation hB
  have h𝓕𝓖 : 𝓕 ≤ 𝓖 := Ito.le_usualAugmentation 𝓕 P
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hδdef
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  set T' : ℕ → Ω → ℝ≥0∞ := fun m ω => gapLoc (δ m) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (T ω)
    with hT'def
  have h104 : ∀ m, ∀ᵐ ω ∂P, T' m ω = 0 := by
    intro m
    refine Aux104.ae_lifetime_eq_zero (𝓕 := 𝓖) (κ := κ) (C := driftBound ρL ρR (δ m))
      (e := fun t ω => distDrift ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t) hB𝓖
      (adaptedBefore_gapLoc h𝓕𝓖 hW hVL hVR (δ m) hW) (adaptedBefore_gapLoc h𝓕𝓖 hW hVL hVR (δ m) (hVL 0))
      (adaptedBefore_gapLoc h𝓕𝓖 hW hVL hVR (δ m) (hVR 0)) hab ?_
    filter_upwards [hpath, hseed] with ω h hs
    exact isSeedEntrance_of_isWordEntrance h hs.1 hs.2.1 gapLoc_le (hδ m) fun t ht =>
      le_gap_of_lt_gapLoc h.continuousOn_w h.continuousOn_vL h.continuousOn_vR ht
  filter_upwards [ae_all_iff.2 h104, hpath, hseed] with ω hT' h hs
  by_contra hT0
  have hTpos : 0 < T ω := pos_iff_ne_zero.2 hT0
  have hlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hevL : ∀ᶠ m in atTop, ∀ i : Fin nL, δ m < W 0 ω - VL i.succ 0 ω :=
    Filter.eventually_all.2 fun i => hlim.eventually (gt_mem_nhds (by
      rw [h.w_zero, h.vL_zero]; linarith [hs.2.2.1 i]))
  have hevR : ∀ᶠ m in atTop, ∀ j : Fin nR, δ m < VR j.succ 0 ω - W 0 ω :=
    Filter.eventually_all.2 fun j => hlim.eventually (gt_mem_nhds (by
      rw [h.w_zero, h.vR_zero]; linarith [hs.2.2.2 j]))
  obtain ⟨m, hmL, hmR⟩ := (hevL.and hevR).exists
  have hpos := gapLoc_pos (δ := δ m) hTpos h.continuousOn_w h.continuousOn_vL h.continuousOn_vR hmL hmR
  exact hpos.ne' (hT' m)

end Prob

/-! ### The nonzero phases are excluded (Aux. lemma 117 + Aux. lemma 104) -/

section Exclusion

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}

/-- Before the positive-gap localization of a word with separated distant marks, the marks at the driver are at most
the seed, so a seed weight different from `−2` makes every colliding total different from `−2`. -/
theorem colliderNe_of_lt_gapLoc {ρ : Fin (nL + 1) → ℝ} (hρ : ρ 0 ≠ -2) {w : ℝ≥0 → ℝ}
    {v : Fin (nL + 1) → ℝ≥0 → ℝ} {u : ℝ≥0} {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i : Fin nL, δ ≤ |w u - v i.succ u|) :
    ColliderNe ρ w v u := by
  have hsub : Finset.univ.filter (fun i => v i u = w u) ⊆ {0} := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_singleton]
    by_contra h0
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 h0
    have := hgap j
    rw [hi.2, sub_self, abs_zero] at this
    linarith
  rcases Finset.subset_singleton_iff.1 hsub with h | h
  · rw [ColliderNe, h, Finset.sum_empty]
    norm_num
  · rw [ColliderNe, h, Finset.sum_singleton]
    exact hρ

/-- **Aux. lemma 122, the nonzero phases are excluded** (p. 391: "Suppose first `n > 0` […] Aux. lemma 104 rules out
such an entrance with (PS9.3). If `n < 0`, the reflected inequalities `a < 0 < b` give the same contradiction"), for
globally defined coordinates. No probability measure carries a driver and geometric force coordinates of a word with
both seeds at `0`, separated distant marks and seed parameters `a = ρ^L_0 + 2`, `b = ρ^R_0 + 2` of opposite signs, whose
explicit coupling means (`coupProc`) are local martingales before swallowing. Applied to the conditional law given the
time-zero event `{d = 2πnχ}` and the shifted word (PS9.2), this says that event is null for `n ≠ 0`
(`PhaseSel.aux122`). -/
theorem false_of_couplingMean_of_opposite [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ}
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hxLd : ∀ i : Fin nL, xL i.succ < 0) (hxRd : ∀ j : Fin nR, 0 < xR j.succ)
    (hab : (0 < ρL 0 + 2 ∧ ρR 0 + 2 < 0) ∨ (0 < ρR 0 + 2 ∧ ρL 0 + 2 < 0))
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    (hmart : ∀ z ∈ QuantumZipper.H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (coupProc κ ρL ρR W VL VR z)) :
    False := by
  obtain ⟨hB, hent⟩ := ae_isWordEntrance_of_couplingMean hκ hW0 hVL0 hVR0 hWc hWa hVLa hVRa hordL hordR
    hpathL hpathR hantiL hmonoR hidxL hidxR hmergeL hmergeR hsep hmart
  set B : ℝ≥0 → Ω → ℝ := fun t ω => MartChar.martProc (MartChar.jointρ ρL ρR) W (MartChar.jointV VL VR) t ω /
    Real.sqrt κ with hBdef
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hB𝓖 := Ito.isFilteredBrownianReal_usualAugmentation hB
  have h𝓕𝓖 : 𝓕 ≤ 𝓖 := Ito.le_usualAugmentation 𝓕 P
  have htop : ∀ X : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓕 X → AdaptedBefore 𝓕 (fun _ => (⊤ : ℝ≥0∞)) X :=
    fun X hX t A hA => by
      simp only [ENNReal.coe_lt_top, true_and]
      exact (hX t).measurable hA
  have hρL : ρL 0 ≠ -2 := by rcases hab with ⟨h1, -⟩ | ⟨-, h2⟩ <;> intro h <;> linarith
  have hρR : ρR 0 ≠ -2 := by rcases hab with ⟨-, h1⟩ | ⟨h2, -⟩ <;> intro h <;> linarith
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hδdef
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  have hcW : ∀ ω, ContinuousOn (W · ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := fun ω => (hWc ω).continuousOn
  have hcL : ∀ ω i, ContinuousOn (fun t => VL i t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := fun ω i =>
    (hpathL ω i).1.continuousOn
  have hcR : ∀ ω j, ContinuousOn (fun t => VR j t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := fun ω j =>
    (hpathR ω j).1.continuousOn
  have hzero : ∀ m, ∀ᵐ ω ∂P, gapLoc (δ m) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) ⊤ = 0 := by
    intro m
    have hadW := adaptedBefore_gapLoc h𝓕𝓖 (htop W hWa) (fun i => htop _ (hVLa i)) (fun j => htop _ (hVRa j))
      (δ m) (htop W hWa)
    have hadL := fun i => adaptedBefore_gapLoc h𝓕𝓖 (htop W hWa) (fun i => htop _ (hVLa i))
      (fun j => htop _ (hVRa j)) (δ m) (htop _ (hVLa i))
    have hadR := fun j => adaptedBefore_gapLoc h𝓕𝓖 (htop W hWa) (fun i => htop _ (hVLa i))
      (fun j => htop _ (hVRa j)) (δ m) (htop _ (hVRa j))
    refine ae_lifetime_eq_zero_of_isWordEntrance (κ := κ) (B := B) (xL := fun _ => xL) (xR := fun _ => xR)
      hB𝓖 hadW hadL hadR hab ?_ (Eventually.of_forall fun _ => ⟨hxL, hxR, hxLd, hxRd⟩)
    filter_upwards [hent] with ω hω
    refine hω _ fun u _ hu => ?_
    obtain ⟨hgL, hgR⟩ := le_gap_of_lt_gapLoc (hcW ω) (hcL ω) (hcR ω) hu
    refine ⟨colliderNe_of_lt_gapLoc hρL (hδ m) fun i => (hgL i).trans (le_abs_self _), ?_⟩
    exact colliderNe_of_lt_gapLoc hρR (hδ m) fun j => by
      rw [abs_sub_comm]; exact (hgR j).trans (le_abs_self _)
  -- for `m` large the localization is positive everywhere
  have hlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hevL : ∀ᶠ m in atTop, ∀ i : Fin nL, δ m < -xL i.succ :=
    Filter.eventually_all.2 fun i => hlim.eventually (gt_mem_nhds (by linarith [hxLd i]))
  have hevR : ∀ᶠ m in atTop, ∀ j : Fin nR, δ m < xR j.succ :=
    Filter.eventually_all.2 fun j => hlim.eventually (gt_mem_nhds (hxRd j))
  obtain ⟨m, hmL, hmR⟩ := (hevL.and hevR).exists
  have hpos : ∀ ω, 0 < gapLoc (δ m) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) ⊤ := fun ω =>
    gapLoc_pos ENNReal.zero_lt_top (hcW ω) (hcL ω) (hcR ω)
      (fun i => by simp only [hW0, hVL0, zero_sub]; exact hmL i)
      (fun j => by simp only [hW0, hVR0, sub_zero]; exact hmR j)
  have hnull : P univ = 0 := by
    have h := hzero m
    rw [ae_iff] at h
    refine measure_mono_null (fun ω _ => ?_) h
    exact (hpos ω).ne'
  simp at hnull

end Exclusion

end PhaseSel

end Sec7

end InteractingSLE
