/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Data.Rat.Cast.Order

/-!
# Recovering the counterflow from a dense family of field-determined points (proof of Proposition 5.13)

Packet PROVE-SEC5-A (specification §5.2, proof of Proposition 5.13, `source/spec/p145-192.md` L91–L140,
pp. 149–151). The deterministic and measure-theoretic steps of the proof:

* the conformal coordinate `ψ(z) = −c/(g_r(Φ(z)) − W_r)`: "`|ψ(z)| > c/a` implies `g_r(Φ(z)) ∈ B(W_r, a)`"
  (`dist_lt_of_lt_norm_neg_div`);
* (5.7) from the rational windows: "Impose this assertion for all positive rational `r, δ`. Every nonempty open
  interval of positive times contains one of the resulting intervals `(r, r+δ]`, proving (5.7)"
  (`exists_mem_Ioo_of_rat_windows`, `dense_of_rat_windows`);
* the recovery: "Enumerate `Γ` using its countable list of prefixes. For fixed `t > 0` and integer `m ≥ 1`, select
  the first point in this enumeration whose recovered time is within `1/m` of `t`. Such a point exists by (5.7). Its
  position tends to `η'(t)` by continuity of the counterflow. This determines `η'(t)` measurably from `h`"
  (`firstNearIndex`, `tendsto_recover`, and `exists_stronglyMeasurable_eq_of_dense`: if the recovered times
  `T n` and points `z n` are `𝒢`-measurable, there is a single `𝒢`-measurable `R` that equals `γ(t)` for every sample
  on which `z n = γ(T n)`, `γ` is continuous at `t` and the times accumulate at `t`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace InteractingSLE

namespace Sec5

/-! ### The conformal coordinate of Proposition 5.13 -/

/-- With `ψ(z) = −c/(g − W)` and `c, a > 0`: `|ψ(z)| > c/a` implies `|g − W| < a`, i.e.
`g_r(Φ(z)) ∈ B(W_r, a)`. -/
theorem dist_lt_of_lt_norm_neg_div {c a : ℝ} (hc : 0 < c) (ha : 0 < a) {g W : ℂ}
    (h : c / a < ‖-(c : ℂ) / (g - W)‖) : dist g W < a := by
  rw [dist_eq_norm]
  by_cases hgW : g - W = 0
  · rw [hgW, div_zero, norm_zero] at h
    exact absurd h (not_lt.2 (div_pos hc ha).le)
  have hn : 0 < ‖g - W‖ := norm_pos_iff.2 hgW
  rw [norm_div, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc.le,
    div_lt_div_iff_of_pos_left hc ha hn] at h
  exact h

/-! ### (5.7) from the rational windows -/

/-- If every rational window `(r, r + δ]` (`r, δ > 0` rational) contains some time `T i`, then every nonempty open
interval of positive times does. -/
theorem exists_mem_Ioo_of_rat_windows {ι : Type*} {T : ι → ℝ}
    (h : ∀ r δ : ℚ, 0 < r → 0 < δ → ∃ i, (r : ℝ) < T i ∧ T i ≤ r + δ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) : ∃ i, T i ∈ Ioo a b := by
  obtain ⟨r, har, hrb⟩ := exists_rat_btwn hab
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (sub_pos.2 hrb)
  have hr0 : (0 : ℝ) < r := ha.trans_lt har
  obtain ⟨i, hi1, hi2⟩ := h r δ (by exact_mod_cast hr0) (by exact_mod_cast hδ0)
  exact ⟨i, har.trans hi1, hi2.trans_lt (by linarith)⟩

/-- (5.7): the times `T i` are dense in `(0, ∞)`: every `t > 0` is a limit of them. -/
theorem dense_of_rat_windows {ι : Type*} {T : ι → ℝ}
    (h : ∀ r δ : ℚ, 0 < r → 0 < δ → ∃ i, (r : ℝ) < T i ∧ T i ≤ r + δ) {t : ℝ} (ht : 0 < t) :
    ∀ ε > 0, ∃ i, |T i - t| < ε := by
  intro ε hε
  obtain ⟨i, hi1, hi2⟩ := exists_mem_Ioo_of_rat_windows h (le_max_right (t - ε / 2) 0)
    (show max (t - ε / 2) 0 < t + ε / 2 from max_lt (by linarith) (by linarith))
  refine ⟨i, abs_sub_lt_iff.2 ⟨by linarith, ?_⟩⟩
  linarith [le_max_left (t - ε / 2) 0]

/-! ### The recovery -/

/-- The accuracy-`m` selection predicate: the time `T n` is within `1/(m+1)` of `t`, or no time is. -/
def NearPred (T : ℕ → ℝ) (t : ℝ) (m n : ℕ) : Prop :=
  |T n - t| < 1 / ((m : ℝ) + 1) ∨ ∀ j, 1 / ((m : ℝ) + 1) ≤ |T j - t|

theorem exists_nearPred (T : ℕ → ℝ) (t : ℝ) (m : ℕ) : ∃ n, NearPred T t m n := by
  by_cases h : ∃ n, |T n - t| < 1 / ((m : ℝ) + 1)
  · obtain ⟨n, hn⟩ := h; exact ⟨n, Or.inl hn⟩
  · push Not at h; exact ⟨0, Or.inr h⟩

open Classical in
/-- "The first point in this enumeration whose recovered time is within `1/m` of `t`" (accuracy `1/(m+1)`). -/
def firstNearIndex (T : ℕ → ℝ) (t : ℝ) (m : ℕ) : ℕ := Nat.find (exists_nearPred T t m)

theorem abs_sub_firstNearIndex_lt {T : ℕ → ℝ} {t : ℝ} {m : ℕ}
    (h : ∃ n, |T n - t| < 1 / ((m : ℝ) + 1)) :
    |T (firstNearIndex T t m) - t| < 1 / ((m : ℝ) + 1) := by
  classical
  rcases Nat.find_spec (exists_nearPred T t m) with h1 | h2
  · exact h1
  · obtain ⟨n, hn⟩ := h; exact absurd (h2 n) (not_le.2 hn)

/-- If the times accumulate at `t`, the selected times converge to `t`. -/
theorem tendsto_firstNearIndex {T : ℕ → ℝ} {t : ℝ} (hd : ∀ ε > 0, ∃ n, |T n - t| < ε) :
    Tendsto (fun m => T (firstNearIndex T t m)) atTop (𝓝 t) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun m hm => ?_⟩
  have hm' : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
  rw [Real.dist_eq]
  exact (abs_sub_firstNearIndex_lt (hd _ (by positivity))).trans_le hm' |>.trans hN

/-- **The recovery**: if `z n = γ(T n)`, `γ` is continuous at `t` and the times accumulate at `t`, the selected
points converge to `γ(t)`. -/
theorem tendsto_recover {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {T : ℕ → ℝ} {z : ℕ → X} {t : ℝ}
    (hγ : ContinuousAt γ t) (hz : ∀ n, z n = γ (T n)) (hd : ∀ ε > 0, ∃ n, |T n - t| < ε) :
    Tendsto (fun m => z (firstNearIndex T t m)) atTop (𝓝 (γ t)) := by
  simp only [hz]
  exact hγ.tendsto.comp (tendsto_firstNearIndex hd)

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω}

theorem measurable_firstNearIndex {T : ℕ → Ω → ℝ} (hT : ∀ n, Measurable[𝒢] (T n)) (t : ℝ) (m : ℕ) :
    Measurable[𝒢] fun ω => firstNearIndex (fun n => T n ω) t m := by
  classical
  refine measurable_find (p := fun ω n => NearPred (fun n => T n ω) t m n)
    (fun ω => exists_nearPred _ t m) fun k => ?_
  simp only [NearPred, ofPred_or, ofPred_forall]
  refine MeasurableSet.union ?_ (MeasurableSet.iInter fun j => ?_)
  · exact measurableSet_lt (continuous_abs.measurable.comp ((hT k).sub_const t)) measurable_const
  · exact measurableSet_le measurable_const (continuous_abs.measurable.comp ((hT j).sub_const t))

/-- Evaluating a family of measurable functions at a measurable index is measurable. -/
theorem measurable_apply_index {X : Type*} [MeasurableSpace X] {z : ℕ → Ω → X}
    (hz : ∀ n, Measurable[𝒢] (z n)) {k : Ω → ℕ} (hk : Measurable[𝒢] k) :
    Measurable[𝒢] fun ω => z (k ω) ω := by
  intro s hs
  have : (fun ω => z (k ω) ω) ⁻¹' s = ⋃ n, (k ⁻¹' {n} ∩ z n ⁻¹' s) := by
    ext ω; simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => ⟨k ω, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  rw [this]
  exact MeasurableSet.iUnion fun n => (hk (measurableSet_singleton n)).inter (hz n hs)

/-- **`η'(t)` is determined measurably** (proof of Proposition 5.13): if the recovered times `T n` and points
`z n` are `𝒢`-measurable (`𝒢 = σ(h)`), there is a `𝒢`-strongly-measurable `R` with `R ω = γ(t)` for every
sample `ω` and every path `γ` continuous at `t` such that `z n ω = γ(T n ω)` for all `n` and the times `T n ω`
accumulate at `t`. -/
theorem exists_stronglyMeasurable_eq_of_dense {T : ℕ → Ω → ℝ} {z : ℕ → Ω → ℂ}
    (hT : ∀ n, Measurable[𝒢] (T n)) (hz : ∀ n, Measurable[𝒢] (z n)) (t : ℝ) :
    ∃ R : Ω → ℂ, StronglyMeasurable[𝒢] R ∧
      ∀ (ω : Ω) (γ : ℝ → ℂ), ContinuousAt γ t → (∀ n, z n ω = γ (T n ω)) →
        (∀ ε > 0, ∃ n, |T n ω - t| < ε) → R ω = γ t := by
  set f : ℕ → Ω → ℂ := fun m ω => z (firstNearIndex (fun n => T n ω) t m) ω with hf
  have hfm : ∀ m, StronglyMeasurable[𝒢] (f m) := fun m =>
    (measurable_apply_index hz (measurable_firstNearIndex hT t m)).stronglyMeasurable
  refine ⟨fun ω => limUnder atTop (fun m => f m ω), StronglyMeasurable.limUnder hfm, ?_⟩
  intro ω γ hγ hzγ hd
  exact (tendsto_recover (T := fun n => T n ω) (z := fun n => z n ω) hγ hzγ hd).limUnder_eq

end Sec5

end InteractingSLE
