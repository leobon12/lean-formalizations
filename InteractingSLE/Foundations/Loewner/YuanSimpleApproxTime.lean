import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Simple approximations of Loewner traces, IV: the stretched time

[Yua22] §4 (`TraceTopology.tex` L479–L497) stretches the time interval: at each cut time `t n` an
extra interval `I_n = [s_n, s_n + h n]` of length `h n` is inserted, during which the
approximating curve runs along the cut segment while the original trace is halted. Here the
original time and the slit fractions are explicit continuous functions of the stretched time `s`:

* `slitStart t h n = t n + ∑_{t m < t n} h m` is the start `s_n` of `I_n`;
* `slitFrac t h n s ∈ [0, 1]` is the fraction of `I_n` traversed by time `s`;
* `origTime t h s = s − ∑ₘ h m · slitFrac t h m s` is the original time (Yuan's `φ⁻¹`).

## Main results

* `continuous_origTime`, `monotone_origTime`: `origTime` is continuous and nondecreasing (the
  total slit length traversed between `s` and `s'` is at most `s' − s`, since the `I_n` are
  disjoint: `slitStart_add_le`);
* `origTime_eq_of_mem`: `origTime = t n` on `I_n`;
* `slitFrac_eq_zero_of_origTime_lt`, `slitFrac_eq_one_of_lt_origTime`: the slit `n` is not yet
  started before the original time reaches `t n`, and complete after it;
* `exists_mem_slit_of_origTime_eq`: two stretched times with the same original time lie in one
  slit interval.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE

namespace YuanSimpleApprox

/-- Total length of the slits inserted before the original time `u`. -/
def slitBefore (t h : ℕ → ℝ) (u : ℝ) : ℝ := ∑' m, if t m < u then h m else 0

/-- Start `s_n = t n + ∑_{t m < t n} h m` of the slit interval `I_n` in the stretched time. -/
def slitStart (t h : ℕ → ℝ) (n : ℕ) : ℝ := t n + slitBefore t h (t n)

/-- Fraction of the slit interval `I_n` traversed by the stretched time `s`. -/
def slitFrac (t h : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ := max 0 (min 1 ((s - slitStart t h n) / h n))

/-- The **original time** of the stretched time `s` (Yuan's `φ⁻¹`). -/
def origTime (t h : ℕ → ℝ) (s : ℝ) : ℝ := s - ∑' m, h m * slitFrac t h m s

variable {t h : ℕ → ℝ}

theorem slitFrac_nonneg (n : ℕ) (s : ℝ) : 0 ≤ slitFrac t h n s := le_max_left _ _

theorem slitFrac_le_one (n : ℕ) (s : ℝ) : slitFrac t h n s ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem continuous_slitFrac (n : ℕ) : Continuous (slitFrac t h n) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const _))

/-- `clamp(s' − a) − clamp(s − a)` is the length of `[a, a + c] ∩ [s, s']`. -/
theorem clamp_sub_clamp {a c s s' : ℝ} (hc : 0 < c) (hss' : s ≤ s') :
    max 0 (min c (s' - a)) - max 0 (min c (s - a)) = max (min (a + c) s' - max a s) 0 := by
  have h1 : min (a + c) s' = a + min c (s' - a) := by
    rw [← min_add_add_left]; congr 1; ring
  have h2 : max a s = a + max 0 (s - a) := by
    rw [← max_add_add_left]; congr 1 <;> ring
  rw [h1, h2, add_sub_add_left_eq_sub]
  rcases le_total (s - a) 0 with hx | hx
  · rw [max_eq_left ((min_le_right _ _).trans hx), max_eq_left hx, sub_zero, sub_zero, max_comm]
  · rcases le_total (s - a) c with hxc | hxc
    · have hy : s - a ≤ s' - a := by linarith
      rw [min_eq_right hxc, max_eq_right hx, max_eq_right (le_min hc.le (hx.trans hy)),
        max_eq_left (sub_nonneg.2 (le_min hxc hy))]
    · rw [min_eq_left hxc, min_eq_left (hxc.trans (by linarith)), max_eq_right hc.le,
        max_eq_right hx, sub_self, max_eq_right (by linarith)]

section Pos

variable (hh : ∀ n, 0 < h n)
include hh

theorem monotone_slitFrac (n : ℕ) : Monotone (slitFrac t h n) := fun s s' hss' =>
  max_le_max le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right (by linarith) (hh n).le))

theorem slitFrac_eq_zero_iff {n : ℕ} {s : ℝ} : slitFrac t h n s = 0 ↔ s ≤ slitStart t h n := by
  constructor
  · intro h0
    by_contra hlt
    rw [not_le] at hlt
    have : 0 < min 1 ((s - slitStart t h n) / h n) :=
      lt_min one_pos (div_pos (by linarith) (hh n))
    have h1 : 0 < slitFrac t h n s := lt_of_lt_of_le this (le_max_right _ _)
    linarith
  · intro hle
    exact max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (hh n).le))

theorem slitFrac_eq_one_iff {n : ℕ} {s : ℝ} :
    slitFrac t h n s = 1 ↔ slitStart t h n + h n ≤ s := by
  constructor
  · intro h1
    by_contra hlt
    rw [not_le] at hlt
    have hlt' : (s - slitStart t h n) / h n < 1 := by
      rw [div_lt_one (hh n)]; linarith
    have : slitFrac t h n s < 1 :=
      max_lt zero_lt_one (lt_of_le_of_lt (min_le_right _ _) hlt')
    linarith
  · intro hle
    have : 1 ≤ (s - slitStart t h n) / h n := by rw [le_div_iff₀ (hh n)]; linarith
    rw [slitFrac, min_eq_left this, max_eq_right zero_le_one]

/-- On the slit interval the fraction is linear. -/
theorem mul_slitFrac_of_mem {n : ℕ} {s : ℝ}
    (hs : s ∈ Icc (slitStart t h n) (slitStart t h n + h n)) :
    h n * slitFrac t h n s = s - slitStart t h n := by
  have h1 : (s - slitStart t h n) / h n ≤ 1 := by rw [div_le_one (hh n)]; linarith [hs.2]
  have h0 : 0 ≤ (s - slitStart t h n) / h n := div_nonneg (by linarith [hs.1]) (hh n).le
  rw [slitFrac, min_eq_right h1, max_eq_right h0, mul_div_cancel₀ _ (hh n).ne']

theorem strictMonoOn_slitFrac (n : ℕ) :
    StrictMonoOn (slitFrac t h n) (Icc (slitStart t h n) (slitStart t h n + h n)) := by
  intro s hs s' hs' hss'
  have e1 := mul_slitFrac_of_mem hh hs
  have e2 := mul_slitFrac_of_mem hh hs'
  by_contra hle
  rw [not_lt] at hle
  have := mul_le_mul_of_nonneg_left hle (hh n).le
  linarith

/-- `h · frac` is the clamp of `s − s_n` to `[0, h]`. -/
theorem mul_slitFrac (n : ℕ) (s : ℝ) :
    h n * slitFrac t h n s = max 0 (min (h n) (s - slitStart t h n)) := by
  rw [slitFrac, mul_max_of_nonneg _ _ (hh n).le, mul_min_of_nonneg _ _ (hh n).le, mul_zero,
    mul_one, mul_div_cancel₀ _ (hh n).ne']

end Pos

section Summable

variable (hh : ∀ n, 0 < h n) (hsum : Summable h)
include hh hsum

theorem summable_ite (u : ℝ) : Summable fun m => if t m < u then h m else 0 :=
  Summable.of_nonneg_of_le (fun m => by split_ifs <;> [exact (hh m).le; exact le_rfl])
    (fun m => by split_ifs <;> [exact le_rfl; exact (hh m).le]) hsum

theorem summable_mul_slitFrac (s : ℝ) : Summable fun m => h m * slitFrac t h m s :=
  Summable.of_nonneg_of_le (fun m => mul_nonneg (hh m).le (slitFrac_nonneg m s))
    (fun m => mul_le_of_le_one_right (hh m).le (slitFrac_le_one m s)) hsum

omit hsum in
theorem slitBefore_nonneg (u : ℝ) : 0 ≤ slitBefore t h u :=
  tsum_nonneg fun m => by split_ifs <;> [exact (hh m).le; exact le_rfl]

/-- The slit `n` is counted in every later `slitBefore`. -/
theorem slitBefore_add_le {n : ℕ} {u : ℝ} (hu : t n < u) :
    slitBefore t h (t n) + h n ≤ slitBefore t h u := by
  have hs1 := summable_ite hh hsum (t := t) (t n)
  have hs2 : Summable fun m => if m = n then h m else 0 :=
    (hasSum_ite_eq n (h n)).summable.congr fun m => by split_ifs with hm <;> simp [hm]
  have heq : ∑' m, (if m = n then h m else 0) = h n := by
    rw [tsum_eq_single n (fun m hm => by simp [hm])]; simp
  rw [slitBefore, ← heq, ← hs1.tsum_add hs2, slitBefore]
  refine (hs1.add hs2).tsum_le_tsum (fun m => ?_) (summable_ite hh hsum u)
  by_cases hm : m = n
  · subst hm; simp [hu]
  · simp only [hm, ite_false, add_zero]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans hu) h2
    · exact (hh m).le
    · exact le_rfl

/-- **The slit intervals are disjoint and ordered as the cut times.** -/
theorem slitStart_add_le {m n : ℕ} (hmn : t m < t n) :
    slitStart t h m + h m ≤ slitStart t h n := by
  have := slitBefore_add_le hh hsum hmn
  rw [slitStart, slitStart]
  linarith

theorem slitBefore_add_le_tsum (n : ℕ) : slitBefore t h (t n) + h n ≤ ∑' m, h m := by
  have hs1 := summable_ite hh hsum (t := t) (t n)
  have hs2 : Summable fun m => if m = n then h m else 0 :=
    (hasSum_ite_eq n (h n)).summable.congr fun m => by split_ifs with hm <;> simp [hm]
  have heq : ∑' m, (if m = n then h m else 0) = h n := by
    rw [tsum_eq_single n (fun m hm => by simp [hm])]; simp
  rw [slitBefore, ← heq, ← hs1.tsum_add hs2]
  refine (hs1.add hs2).tsum_le_tsum (fun m => ?_) hsum
  by_cases hm : m = n
  · subst hm; simp
  · simp only [hm, ite_false, add_zero]
    split_ifs
    · exact le_rfl
    · exact (hh m).le

omit hsum in
theorem tsum_mul_slitFrac_nonneg (s : ℝ) : 0 ≤ ∑' m, h m * slitFrac t h m s :=
  tsum_nonneg fun m => mul_nonneg (hh m).le (slitFrac_nonneg m s)

theorem tsum_mul_slitFrac_le (s : ℝ) : ∑' m, h m * slitFrac t h m s ≤ ∑' m, h m :=
  (summable_mul_slitFrac hh hsum s).tsum_le_tsum
    (fun m => mul_le_of_le_one_right (hh m).le (slitFrac_le_one m s)) hsum

theorem continuous_origTime : Continuous (origTime t h) := by
  refine continuous_id.sub (continuous_tsum (fun m => continuous_const.mul (continuous_slitFrac m))
    hsum fun m s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hh m).le (slitFrac_nonneg m s))]
  exact mul_le_of_le_one_right (hh m).le (slitFrac_le_one m s)

omit hsum in
theorem origTime_le (s : ℝ) : origTime t h s ≤ s := by
  have := tsum_mul_slitFrac_nonneg hh (t := t) s
  rw [origTime]; linarith

theorem le_origTime (s : ℝ) : s - ∑' m, h m ≤ origTime t h s := by
  have := tsum_mul_slitFrac_le hh hsum (t := t) s
  rw [origTime]; linarith

/-- **The slit length traversed between `s ≤ s'` is at most `s' − s`** (the slit intervals are
disjoint). -/
theorem tsum_mul_slitFrac_sub_le (ht : Function.Injective t) {s s' : ℝ} (hss' : s ≤ s') :
    ∑' m, h m * slitFrac t h m s' - ∑' m, h m * slitFrac t h m s ≤ s' - s := by
  rw [← (summable_mul_slitFrac hh hsum s').tsum_sub (summable_mul_slitFrac hh hsum s)]
  set A : ℕ → Set ℝ := fun m => Ioo (slitStart t h m) (slitStart t h m + h m) ∩ Ioo s s' with hA
  have hgA : ∀ m, h m * slitFrac t h m s' - h m * slitFrac t h m s = (volume (A m)).toReal := by
    intro m
    rw [mul_slitFrac hh, mul_slitFrac hh, clamp_sub_clamp (hh m) hss', hA]
    simp only
    rw [Ioo_inter_Ioo, Real.volume_Ioo, ENNReal.toReal_ofReal']
  have hfin : ∀ m, volume (A m) ≠ ⊤ := fun m =>
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hdisj : ∀ F : Finset ℕ, (F : Set ℕ).PairwiseDisjoint A := by
    intro F m _ m' _ hmm'
    have hne : t m ≠ t m' := fun h' => hmm' (ht h')
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := slitStart_add_le hh hsum hlt
      exact Set.disjoint_left.2 fun x hx hx' => by linarith [hx.1.2, hx'.1.1]
    · have := slitStart_add_le hh hsum hlt
      exact Set.disjoint_left.2 fun x hx hx' => by linarith [hx.1.1, hx'.1.2]
  refine ((summable_mul_slitFrac hh hsum s').sub
    (summable_mul_slitFrac hh hsum s)).tsum_le_of_sum_le
    fun F => ?_
  simp_rw [hgA]
  rw [← ENNReal.toReal_sum fun m _ => hfin m, ← measure_biUnion_finset (hdisj F)
    (fun m _ => measurableSet_Ioo.inter measurableSet_Ioo)]
  have hsub : (⋃ m ∈ F, A m) ⊆ Ioo s s' := iUnion₂_subset fun m _ => inter_subset_right
  calc (volume (⋃ m ∈ F, A m)).toReal ≤ (volume (Ioo s s')).toReal :=
        ENNReal.toReal_mono (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
          (measure_mono hsub)
    _ = s' - s := by rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]

theorem monotone_origTime (ht : Function.Injective t) : Monotone (origTime t h) :=
  fun s s' hss' => by
    have := tsum_mul_slitFrac_sub_le hh hsum ht hss'
    simp only [origTime]
    linarith

/-- **On the slit interval `I_n` the original time is `t n`.** -/
theorem origTime_eq_of_mem (ht : Function.Injective t) {n : ℕ} {s : ℝ}
    (hs : s ∈ Icc (slitStart t h n) (slitStart t h n + h n)) : origTime t h s = t n := by
  have hterm : ∀ m, h m * slitFrac t h m s =
      (if t m < t n then h m else 0) + (if m = n then s - slitStart t h n else 0) := by
    intro m
    by_cases hm : m = n
    · subst hm
      simp only [lt_self_iff_false, ite_false, ite_true, zero_add]
      exact mul_slitFrac_of_mem hh hs
    · simp only [hm, ite_false, add_zero]
      have hne : t m ≠ t n := fun h' => hm (ht h')
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · rw [(slitFrac_eq_one_iff hh).2 ((slitStart_add_le hh hsum hlt).trans hs.1), mul_one]
        simp [hlt]
      · rw [(slitFrac_eq_zero_iff hh).2 (hs.2.trans (slitStart_add_le hh hsum hlt)), mul_zero]
        simp [not_lt.2 hlt.le]
  have hs2 : Summable fun m => if m = n then s - slitStart t h n else 0 :=
    (hasSum_ite_eq n (s - slitStart t h n)).summable
  rw [origTime, tsum_congr hterm, (summable_ite hh hsum (t n)).tsum_add hs2, tsum_ite_eq]
  change s - (slitBefore t h (t n) + (s - slitStart t h n)) = t n
  rw [slitStart]
  ring

theorem slitFrac_eq_zero_of_origTime_lt (ht : Function.Injective t) {n : ℕ} {s : ℝ}
    (hs : origTime t h s < t n) : slitFrac t h n s = 0 := by
  by_contra hne
  have hlt : slitStart t h n < s := not_le.1 fun hle => hne ((slitFrac_eq_zero_iff hh).2 hle)
  have := monotone_origTime hh hsum ht hlt.le
  rw [origTime_eq_of_mem hh hsum ht ⟨le_rfl, by linarith [hh n]⟩] at this
  linarith

theorem slitFrac_eq_one_of_lt_origTime (ht : Function.Injective t) {n : ℕ} {s : ℝ}
    (hs : t n < origTime t h s) : slitFrac t h n s = 1 := by
  by_contra hne
  have hlt : s < slitStart t h n + h n :=
    not_le.1 fun hle => hne ((slitFrac_eq_one_iff hh).2 hle)
  have := monotone_origTime hh hsum ht hlt.le
  rw [origTime_eq_of_mem hh hsum ht ⟨by linarith [hh n], le_rfl⟩] at this
  linarith

theorem origTime_ge_of_slitFrac_pos (ht : Function.Injective t) {n : ℕ} {s : ℝ}
    (hs : 0 < slitFrac t h n s) : t n ≤ origTime t h s :=
  not_lt.1 fun hlt => hs.ne' (slitFrac_eq_zero_of_origTime_lt hh hsum ht hlt)

theorem origTime_le_of_slitFrac_lt_one (ht : Function.Injective t) {n : ℕ} {s : ℝ}
    (hs : slitFrac t h n s < 1) : origTime t h s ≤ t n :=
  not_lt.1 fun hlt => hs.ne (slitFrac_eq_one_of_lt_origTime hh hsum ht hlt)

omit hsum in
theorem slitStart_nonneg (ht0 : ∀ n, 0 ≤ t n) (n : ℕ) : 0 ≤ slitStart t h n :=
  add_nonneg (ht0 n) (slitBefore_nonneg hh _)

omit hsum in
theorem origTime_zero (ht0 : ∀ n, 0 ≤ t n) : origTime t h 0 = 0 := by
  have : ∀ m, h m * slitFrac t h m 0 = 0 := fun m => by
    rw [(slitFrac_eq_zero_iff hh).2 (slitStart_nonneg hh ht0 m), mul_zero]
  rw [origTime, tsum_congr this, tsum_zero, sub_zero]

theorem slitStart_add_le_end {S : ℝ} (htS : ∀ n, t n < S) (n : ℕ) :
    slitStart t h n + h n ≤ S + ∑' m, h m := by
  have := slitBefore_add_le_tsum hh hsum (t := t) n
  rw [slitStart]; linarith [htS n]

theorem origTime_end {S : ℝ} (htS : ∀ n, t n < S) : origTime t h (S + ∑' m, h m) = S := by
  have : ∀ m, h m * slitFrac t h m (S + ∑' m, h m) = h m := fun m => by
    rw [(slitFrac_eq_one_iff hh).2 (slitStart_add_le_end hh hsum htS m), mul_one]
  rw [origTime, tsum_congr this]
  ring

/-- **Fibres of the original time**: two stretched times with the same original time lie in one
slit interval. -/
theorem exists_mem_slit_of_origTime_eq (ht : Function.Injective t) {s s' : ℝ} (hss' : s < s')
    (heq : origTime t h s = origTime t h s') :
    ∃ n, s ∈ Icc (slitStart t h n) (slitStart t h n + h n) ∧
      s' ∈ Icc (slitStart t h n) (slitStart t h n + h n) := by
  set g : ℕ → ℝ := fun m => h m * slitFrac t h m s' - h m * slitFrac t h m s with hg
  have hgs : Summable g := (summable_mul_slitFrac hh hsum s').sub (summable_mul_slitFrac hh hsum s)
  have hsumg : ∑' m, g m = s' - s := by
    rw [hg, (summable_mul_slitFrac hh hsum s').tsum_sub (summable_mul_slitFrac hh hsum s)]
    simp only [origTime] at heq
    linarith
  have hg0 : ∀ m, 0 ≤ g m := fun m =>
    sub_nonneg.2 (mul_le_mul_of_nonneg_left (monotone_slitFrac hh m hss'.le) (hh m).le)
  obtain ⟨n, hn⟩ : ∃ n, 0 < g n := by
    by_contra hall
    push Not at hall
    have : ∑' m, g m ≤ 0 := tsum_nonpos hall
    linarith
  have hfrac : slitFrac t h n s < slitFrac t h n s' := by
    by_contra hle
    rw [not_lt] at hle
    have := mul_le_mul_of_nonneg_left hle (hh n).le
    simp only [hg] at hn
    linarith
  have h1 : t n ≤ origTime t h s' :=
    origTime_ge_of_slitFrac_pos hh hsum ht (lt_of_le_of_lt (slitFrac_nonneg n s) hfrac)
  have h2 : origTime t h s ≤ t n :=
    origTime_le_of_slitFrac_lt_one hh hsum ht (lt_of_lt_of_le hfrac (slitFrac_le_one n s'))
  have hτ : origTime t h s = t n := le_antisymm h2 (heq ▸ h1)
  have hτ' : origTime t h s' = t n := heq ▸ hτ
  -- the other slits do not move
  have hother : ∀ m, m ≠ n → g m = 0 := by
    intro m hm
    have hne : t m ≠ t n := fun h' => hm (ht h')
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [hg]; simp only
      rw [slitFrac_eq_one_of_lt_origTime hh hsum ht (by rw [hτ']; exact hlt),
        slitFrac_eq_one_of_lt_origTime hh hsum ht (by rw [hτ]; exact hlt), sub_self]
    · rw [hg]; simp only
      rw [slitFrac_eq_zero_of_origTime_lt hh hsum ht (by rw [hτ']; exact hlt),
        slitFrac_eq_zero_of_origTime_lt hh hsum ht (by rw [hτ]; exact hlt), sub_self]
  have hgn : g n = s' - s := by rw [← hsumg, tsum_eq_single n hother]
  have hclamp : max 0 (min (h n) (s' - slitStart t h n)) - max 0 (min (h n) (s - slitStart t h n))
      = s' - s := by
    rw [← mul_slitFrac hh, ← mul_slitFrac hh]; exact hgn
  have hs_lt : s < slitStart t h n + h n := by
    by_contra hle
    rw [not_lt] at hle
    have := (slitFrac_eq_one_iff hh).2 hle
    linarith [slitFrac_le_one (t := t) (h := h) n s']
  refine ⟨n, ⟨?_, hs_lt.le⟩, ⟨?_, ?_⟩⟩
  · by_contra hlt
    rw [not_le] at hlt
    have e0 : max 0 (min (h n) (s - slitStart t h n)) = 0 :=
      max_eq_left ((min_le_right _ _).trans (by linarith))
    rw [e0, sub_zero] at hclamp
    have : max 0 (min (h n) (s' - slitStart t h n)) ≤ max 0 (s' - slitStart t h n) :=
      max_le_max le_rfl (min_le_right _ _)
    have : max 0 (s' - slitStart t h n) < s' - s := max_lt (by linarith) (by linarith)
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    have e0 : max 0 (min (h n) (s - slitStart t h n)) = 0 :=
      max_eq_left ((min_le_right _ _).trans (by linarith))
    rw [e0, sub_zero] at hclamp
    have : max 0 (min (h n) (s' - slitStart t h n)) ≤ max 0 (s' - slitStart t h n) :=
      max_le_max le_rfl (min_le_right _ _)
    have : max 0 (s' - slitStart t h n) < s' - s := max_lt (by linarith) (by linarith)
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    have e1 : max 0 (min (h n) (s' - slitStart t h n)) = h n := by
      rw [min_eq_left (by linarith), max_eq_right (hh n).le]
    rw [e1] at hclamp
    have : s - slitStart t h n ≤ max 0 (min (h n) (s - slitStart t h n)) :=
      le_max_of_le_right (le_min (by linarith) le_rfl)
    linarith

end Summable

end YuanSimpleApprox

end InteractingSLE
