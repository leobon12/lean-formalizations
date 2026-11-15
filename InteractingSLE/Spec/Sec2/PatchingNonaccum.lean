/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalEscape
import InteractingSLE.Spec.Sec2.AddMarksPath

/-!
# Nonaccumulation of changes of the active mark

Packet PROVE-SEC2-TERM2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md` L494),
graph node `SPEC.thm-2.2#nonaccumulation`: in the iterated patching of the local constructions,
after the same-side mergers have stopped, changes of the active mark alternate between the two
sides; fix a time `t₀` with the nearest marks separated, `L = V^{1,L}_{t₀} < R = V^{1,R}_{t₀}`;
every passage of the driver across the middle third of `[L, R]` takes at least a random `δ > 0`
(Brownian uniform continuity and the bounded drift in the middle third), so infinitely many
alternations cannot occur before a finite time. "This argument does not presuppose continuity of
`W` at that lifetime."

The statement is made for local solutions `Sec2.IsSLEPathUpTo` (PROVE-SEC2-GIR2: every condition
of Definition 2.1 before a time `τ`, without maximality), which is what a concatenation of local
constructions is before the supremum of its stage times:

* `exists_pos_crossing_time_of_increment`: a generic crossing-time bound for a function whose
  increments in a strip are controlled by a uniformly continuous `b` and a bounded drift;
* `not_alternating_of_crossing`: a crossing-time bound excludes infinitely many alternations;
* **`IsSLEPathUpTo.not_alternating`**: for a local solution before `τ`, a finite `T ≤ τ` with `b`
  continuous on `[0, T]`, and separated marks at `t₀ < T`, there is no monotone sequence of
  times in `[t₀, T)` at which the driver is alternately `≤ L` and `≥ R`.

Monotonicity of the force points and the increment of the driver for local solutions
(`IsSLEPathUpTo.vL_le_of_le`, `le_vR_of_le`, `w_sub`) are proved along the way.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-! ### Generic crossing and counting -/

/-- **Crossing-time bound** from an increment estimate: if in the strip `(α, β)` the increments of
`w` after `t₀` satisfy `|w_q − w_p| ≤ k |b_q − b_p| + C (q − p)` and `b` is continuous on
`[0, T]`, then a full passage across the strip takes at least some `δ > 0`. -/
theorem exists_pos_crossing_time_of_increment {w b : ℝ≥0 → ℝ} {T t₀ : ℝ≥0} {k C α β : ℝ}
    (hb : ContinuousOn b (Icc 0 T)) (hαβ : α < β) (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hinc : ∀ p q : ℝ≥0, t₀ ≤ p → p ≤ q → q < T →
      (∀ s, p < s → s < q → α < w s ∧ w s < β) →
      |w q - w p| ≤ k * |b q - b p| + C * ((q : ℝ) - p)) :
    ∃ δ > 0, ∀ p q : ℝ≥0, t₀ ≤ p → p ≤ q → q < T →
      (∀ s, p < s → s < q → α < w s ∧ w s < β) → β - α ≤ |w q - w p| → δ ≤ (q : ℝ) - p := by
  set d := β - α with hd
  have hd0 : 0 < d := sub_pos.2 hαβ
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hb
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := huc (d / (2 * (k + 1))) (by positivity)
  refine ⟨min δ₁ (d / (2 * (C + 1))), lt_min hδ₁ (by positivity),
    fun p q hp hpq hqT hstrip hcross => ?_⟩
  by_contra hcon
  have hqp : (q : ℝ) - p < min δ₁ (d / (2 * (C + 1))) := not_le.1 hcon
  have hqp0 : (0 : ℝ) ≤ (q : ℝ) - p := sub_nonneg.2 (by exact_mod_cast hpq)
  have hbqp : |b q - b p| < d / (2 * (k + 1)) := by
    have hdist : dist q p < δ₁ := by
      rw [NNReal.dist_eq, abs_of_nonneg hqp0]
      exact hqp.trans_le (min_le_left _ _)
    have := hδ₁b q ⟨zero_le, hqT.le⟩ p ⟨zero_le, hpq.trans hqT.le⟩ hdist
    rwa [Real.dist_eq] at this
  have h2 : k * |b q - b p| < d / 2 := by
    calc k * |b q - b p| ≤ (k + 1) * |b q - b p| := by nlinarith [abs_nonneg (b q - b p)]
      _ < (k + 1) * (d / (2 * (k + 1))) := mul_lt_mul_of_pos_left hbqp (by positivity)
      _ = d / 2 := by field_simp
  have h3 : C * ((q : ℝ) - p) < d / 2 := by
    calc C * ((q : ℝ) - p) ≤ C * (d / (2 * (C + 1))) :=
          mul_le_mul_of_nonneg_left (hqp.le.trans (min_le_right _ _)) hC
      _ < d / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have := hinc p q hp hpq hqT hstrip
  linarith

/-- **Finitely many alternations** (Specification p. 22, "infinitely many alternating passages
cannot occur by time `T`"): if every passage of a continuous `w` across `(α, β)` inside `[t₀, T)`
takes at least `δ > 0`, there is no monotone sequence of times in `[t₀, T)` at which `w` is
alternately `≤ α` and `≥ β`. -/
theorem not_alternating_of_crossing {w : ℝ≥0 → ℝ} {t₀ T : ℝ≥0} {α β δ : ℝ} (hαβ : α ≤ β)
    (hδ : 0 < δ) (hw : ContinuousOn w (Ico t₀ T))
    (hcross : ∀ p q : ℝ≥0, t₀ ≤ p → p ≤ q → q < T →
      (∀ s, p < s → s < q → α < w s ∧ w s < β) → β - α ≤ |w q - w p| → δ ≤ (q : ℝ) - p) :
    ¬ ∃ s : ℕ → ℝ≥0, Monotone s ∧ (∀ k, t₀ ≤ s k ∧ s k < T) ∧
      ∀ k, w (s (2 * k)) ≤ α ∧ β ≤ w (s (2 * k + 1)) := by
  rintro ⟨s, hmono, hrange, halt⟩
  have hstep : ∀ k, δ ≤ (s (2 * k + 1) : ℝ) - s (2 * k) := fun k => by
    have huv : s (2 * k) ≤ s (2 * k + 1) := hmono (by omega)
    have hcont : ContinuousOn w (Icc (s (2 * k)) (s (2 * k + 1))) :=
      hw.mono fun r hr => ⟨(hrange _).1.trans hr.1, hr.2.trans_lt (hrange _).2⟩
    obtain ⟨u', v', hu', huv', hv', hwu, hwv, hstrip⟩ :=
      exists_crossing huv hcont (halt k).1 (halt k).2
    have hc := hcross u' v' ((hrange _).1.trans hu') huv' (hv'.trans_lt (hrange _).2) hstrip
      (by rw [abs_of_nonneg (by linarith)]; linarith)
    have : (u' : ℝ) ≥ s (2 * k) := by exact_mod_cast hu'
    have : (v' : ℝ) ≤ s (2 * k + 1) := by exact_mod_cast hv'
    linarith
  have hind : ∀ k : ℕ, (s 0 : ℝ) + k * δ ≤ s (2 * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hstep k
      have h2 : (s (2 * k + 1) : ℝ) ≤ s (2 * (k + 1)) := by exact_mod_cast hmono (by omega)
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((T : ℝ) / δ)
  have h1 := hind k
  have h2 : (s (2 * k) : ℝ) < T := by exact_mod_cast (hrange (2 * k)).2
  have h3 : (T : ℝ) < k * δ := by rwa [div_lt_iff₀ hδ] at hk
  have h4 : (0 : ℝ) ≤ s 0 := NNReal.coe_nonneg _
  linarith

/-! ### Local solutions -/

namespace IsSLEPathUpTo

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

variable (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
include h

theorem intervalIntegrable_forceL {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) (i : Fin nL) :
    IntervalIntegrable (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0 t := by
  have := (h.integrable_gapL ht i).const_mul (-2)
  simpa only [two_div_sub_eq] using this

theorem intervalIntegrable_forceR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) (i : Fin nR) :
    IntervalIntegrable (fun s : ℝ => 2 / (vR i s.toNNReal - w s.toNNReal)) volume 0 t := by
  have := (h.integrable_gapR ht i).const_mul (-2)
  simpa only [two_div_sub_eq] using this

theorem intervalIntegrable_driverDrift {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) :
    IntervalIntegrable (driverDrift ρL ρR w vL vR) volume 0 t := by
  have hL := IntervalIntegrable.sum Finset.univ fun i _ => by
    simpa only [div_eq_mul_inv] using (h.integrable_gapL ht i).const_mul (ρL i)
  have hR := IntervalIntegrable.sum Finset.univ fun i _ => by
    simpa only [div_eq_mul_inv] using (h.integrable_gapR ht i).const_mul (ρR i)
  rw [Finset.sum_fn] at hL hR
  exact hL.add hR

/-- The driving equation with the drift collected. -/
theorem w_eq_integral_driverDrift {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) :
    w t = Real.sqrt a * b t + ∫ s in (0 : ℝ)..t, driverDrift ρL ρR w vL vR s := by
  have hL : ∀ i ∈ Finset.univ, IntervalIntegrable
      (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := fun i _ => by
    simpa only [div_eq_mul_inv] using (h.integrable_gapL ht i).const_mul (ρL i)
  have hR : ∀ i ∈ Finset.univ, IntervalIntegrable
      (fun s : ℝ => ρR i / (w s.toNNReal - vR i s.toNNReal)) volume 0 t := fun i _ => by
    simpa only [div_eq_mul_inv] using (h.integrable_gapR ht i).const_mul (ρR i)
  have hL' := IntervalIntegrable.sum Finset.univ hL
  have hR' := IntervalIntegrable.sum Finset.univ hR
  rw [Finset.sum_fn] at hL' hR'
  rw [h.w_eq ht, add_assoc, ← intervalIntegral.integral_finsetSum hL,
    ← intervalIntegral.integral_finsetSum hR, ← intervalIntegral.integral_add hL' hR']
  rfl

/-- Increment of the driver of a local solution. -/
theorem w_sub {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < τ) :
    w t - w s = Real.sqrt a * (b t - b s)
      + ∫ r in (s : ℝ)..t, driverDrift ρL ρR w vL vR r := by
  have hs : (s : ℝ≥0∞) < τ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  rw [h.w_eq_integral_driverDrift ht, h.w_eq_integral_driverDrift hs,
    ← intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_driverDrift ht)
      (h.intervalIntegrable_driverDrift hs)]
  ring

/-- Each left force point of a local solution is nonincreasing. -/
theorem vL_le_of_le {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < τ) (i : Fin nL) :
    vL i t ≤ vL i s := by
  have hs : (s : ℝ≥0∞) < τ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hint : IntervalIntegrable (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) volume s t :=
    (h.intervalIntegrable_forceL ht i).mono_set (by
      rw [uIcc_of_le hst', uIcc_of_le (NNReal.coe_nonneg t)]
      exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl)
  have hle : ∫ r in (s : ℝ)..t, 2 / (vL i r.toNNReal - w r.toNNReal) ≤
      ∫ _ in (s : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_mono_on hst' hint intervalIntegrable_const fun r hr => ?_
    have hr0 : r ∈ Icc (0 : ℝ) t := ⟨(NNReal.coe_nonneg s).trans hr.1, hr.2⟩
    exact div_nonpos_of_nonneg_of_nonpos (by norm_num)
      (sub_nonpos.2 (h.vL_le_w (toNNReal_lt_of_mem_Icc ht hr0) i))
  have e : vL i t - vL i s = ∫ r in (s : ℝ)..t, 2 / (vL i r.toNNReal - w r.toNNReal) := by
    rw [h.vL_eq ht i, h.vL_eq hs i, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_forceL ht i)
        (h.intervalIntegrable_forceL hs i)]
  rw [intervalIntegral.integral_zero, ← e] at hle
  linarith

/-- Each right force point of a local solution is nondecreasing. -/
theorem le_vR_of_le {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < τ) (i : Fin nR) :
    vR i s ≤ vR i t := by
  have hs : (s : ℝ≥0∞) < τ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hint : IntervalIntegrable (fun r : ℝ => 2 / (vR i r.toNNReal - w r.toNNReal)) volume s t :=
    (h.intervalIntegrable_forceR ht i).mono_set (by
      rw [uIcc_of_le hst', uIcc_of_le (NNReal.coe_nonneg t)]
      exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl)
  have hle : ∫ _ in (s : ℝ)..t, (0 : ℝ) ≤
      ∫ r in (s : ℝ)..t, 2 / (vR i r.toNNReal - w r.toNNReal) := by
    refine intervalIntegral.integral_mono_on hst' intervalIntegrable_const hint fun r hr => ?_
    have hr0 : r ∈ Icc (0 : ℝ) t := ⟨(NNReal.coe_nonneg s).trans hr.1, hr.2⟩
    exact div_nonneg (by norm_num)
      (sub_nonneg.2 (h.w_le_vR (toNNReal_lt_of_mem_Icc ht hr0) i))
  have e : vR i t - vR i s = ∫ r in (s : ℝ)..t, 2 / (vR i r.toNNReal - w r.toNNReal) := by
    rw [h.vR_eq ht i, h.vR_eq hs i, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_forceR ht i)
        (h.intervalIntegrable_forceR hs i)]
  rw [intervalIntegral.integral_zero, ← e] at hle
  linarith

/-- **Nonaccumulation of changes of the active mark** (Specification p. 22, graph node
`SPEC.thm-2.2#nonaccumulation`): for a local solution before `τ`, a finite horizon `T ≤ τ` with the
driving path `b` continuous on `[0, T]`, and a time `t₀ < T` at which all left marks are at most
`L` and all right marks at least `R > L`, the driver cannot be alternately `≤ L` (at a left mark)
and `≥ R` (at a right mark) along a monotone sequence of times in `[t₀, T)`. Continuity of `w` at
`T` is not used. -/
theorem not_alternating {T : ℝ≥0} (hT : (T : ℝ≥0∞) ≤ τ) (hb : ContinuousOn b (Icc 0 T))
    {t₀ : ℝ≥0} {L R : ℝ} (hLR : L < R) (hL : ∀ i, vL i t₀ ≤ L) (hR : ∀ j, R ≤ vR j t₀) :
    ¬ ∃ s : ℕ → ℝ≥0, Monotone s ∧ (∀ k, t₀ ≤ s k ∧ s k < T) ∧
      ∀ k, w (s (2 * k)) ≤ L ∧ R ≤ w (s (2 * k + 1)) := by
  set d := R - L with hd
  have hd0 : 0 < d := sub_pos.2 hLR
  have hlt : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < τ := fun s hs =>
    lt_of_lt_of_le (by exact_mod_cast hs) hT
  set K := ∑ i, |ρL i| + ∑ j, |ρR j| with hK
  have hK0 : 0 ≤ K := add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  -- separation after `t₀`
  have hsep : ∀ s : ℝ≥0, t₀ ≤ s → s < T → (∀ i, vL i s ≤ L) ∧ ∀ j, R ≤ vR j s := fun s hs hsT =>
    ⟨fun i => (h.vL_le_of_le hs (hlt s hsT) i).trans (hL i),
      fun j => (hR j).trans (h.le_vR_of_le hs (hlt s hsT) j)⟩
  have hinc : ∀ p q : ℝ≥0, t₀ ≤ p → p ≤ q → q < T →
      (∀ s, p < s → s < q → L + d / 3 < w s ∧ w s < R - d / 3) →
      |w q - w p| ≤ Real.sqrt a * |b q - b p| + K / (d / 3) * ((q : ℝ) - p) := by
    intro p q hp hpq hqT hstrip
    have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
    have hint : ‖∫ r in (p : ℝ)..q, driverDrift ρL ρR w vL vR r‖ ≤
        K / (d / 3) * |(q : ℝ) - p| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
      filter_upwards [Measure.ae_ne volume (q : ℝ)] with r hrq hr
      rw [uIoc_of_le hpq'] at hr
      rw [Real.norm_eq_abs]
      have hp' : p < r.toNNReal := Real.lt_toNNReal_iff_coe_lt.2 hr.1
      have hq' : r.toNNReal < q :=
        (Real.toNNReal_lt_iff_lt_coe ((NNReal.coe_nonneg p).trans hr.1.le)).2
          (lt_of_le_of_ne hr.2 hrq)
      obtain ⟨hL', hR'⟩ := hsep _ (hp.trans hp'.le) (hq'.trans hqT)
      obtain ⟨h1, h2⟩ := hstrip _ hp' hq'
      exact abs_driverDrift_le (by positivity) hL' hR' h1.le h2.le
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hpq')] at hint
    rw [h.w_sub hpq (hlt q hqT)]
    calc |Real.sqrt a * (b q - b p) + ∫ r in (p : ℝ)..q, driverDrift ρL ρR w vL vR r|
        ≤ |Real.sqrt a * (b q - b p)| + |∫ r in (p : ℝ)..q, driverDrift ρL ρR w vL vR r| :=
          abs_add_le _ _
      _ ≤ Real.sqrt a * |b q - b p| + K / (d / 3) * ((q : ℝ) - p) := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg a)]
          exact add_le_add le_rfl hint
  obtain ⟨δ, hδ, hcross⟩ := exists_pos_crossing_time_of_increment (w := w) (t₀ := t₀) hb
    (show L + d / 3 < R - d / 3 by linarith) (Real.sqrt_nonneg a)
    (div_nonneg hK0 (by positivity)) hinc
  rintro ⟨s, hmono, hrange, halt⟩
  refine not_alternating_of_crossing (by linarith) hδ
    (h.continuousOn_w.mono fun r hr => hlt r hr.2) hcross
    ⟨s, hmono, hrange, fun k => ⟨(halt k).1.trans (by linarith : L ≤ L + d / 3),
      le_trans (by linarith : R - d / 3 ≤ R) (halt k).2⟩⟩

end IsSLEPathUpTo

end Sec2

end InteractingSLE
