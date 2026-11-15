/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHStmt
import InteractingSLE.Spec.Sec2.Assembly3Law
import InteractingSLE.Spec.Sec7.CounterflowProbDilation

/-!
# The local stop read from a code, and level pauses

Packet PROVE-LOCEXT-J, input (U) of Aux. lemma 54. The local stop `S = r²/64 ∧ inf{t : |W_t| > r/4}` is a **strict**
hitting time: it looks a little beyond `S`. When a stopped coupling is continued after `S` by fresh randomness, the
continued driver need not exceed `r/4` immediately after `S`; the continued local stop is still `S` unless the continued
driver **pauses at the level**: it reaches `|w| ≥ r/4` at some `t₀` and stays `|w| ≤ r/4` on `[0, t₁]` for some
`t₁ > t₀` (`IsLevelPause`, `localStopPath_eq_of_not_isLevelPause`). This file proves the path facts about pauses:

* the levels at which a path pauses form a countable set (`countable_setOf_isLevelPause`: the pause intervals of two
  levels are disjoint, each contains a rational);
* pauses scale with the dilation `t ↦ (√c)⁻¹ w(ct)` (`isLevelPause_dilPath_iff`);
* for continuous paths pauses and the local stop are read from countably many times (`isLevelPause_iff_dense`,
  `localStopPath_top_lt_iff`);

and reads everything from the dyadic codes `ℕ × ℕ → StateSp nL nR` of Theorem 2.2's uniqueness proof (`GCode`): the
pause event is jointly measurable in the level and the code (`measurableSet_pauseSet`), the local stop of the decoded
driver is measurable (`measurable_locStopCode`), and so is the **two-seed history read from a code** (`histOfCode`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Coupling Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3

/-! ### Level pauses of a path -/

section Pause

variable {w : ℝ≥0 → ℝ}

/-- **The path pauses at level `a`**: `|w| ≥ a` at some time `t₀`, and `|w| ≤ a` on `[0, t₁]` for some `t₁ > t₀`. -/
def IsLevelPause (a : ℝ) (w : ℝ≥0 → ℝ) : Prop :=
  ∃ t₀ t₁ : ℝ≥0, t₀ < t₁ ∧ a ≤ |w t₀| ∧ ∀ s ≤ t₁, |w s| ≤ a

/-- **A path pauses at countably many levels.** The pause windows `(t₀, t₁)` of two different levels are disjoint;
each contains a rational. -/
theorem countable_setOf_isLevelPause (w : ℝ≥0 → ℝ) : {a : ℝ | IsLevelPause a w}.Countable := by
  classical
  have key : ∀ a ∈ {a : ℝ | IsLevelPause a w}, ∃ q : ℚ, ∃ t₀ t₁ : ℝ≥0, (t₀ : ℝ) < q ∧ (q : ℝ) < t₁ ∧
      a ≤ |w t₀| ∧ ∀ s ≤ t₁, |w s| ≤ a := by
    rintro a ⟨t₀, t₁, h01, h0, h1⟩
    obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (show (t₀ : ℝ) < t₁ by exact_mod_cast h01)
    exact ⟨q, t₀, t₁, hq0, hq1, h0, h1⟩
  choose! f hf using key
  refine MapsTo.countable_of_injOn (f := f) (mapsTo_univ _ _) ?_ (Set.countable_univ)
  -- disjointness of the windows
  have hlt : ∀ a ∈ {a : ℝ | IsLevelPause a w}, ∀ b ∈ {a : ℝ | IsLevelPause a w}, a < b → (f a : ℝ) < f b := by
    intro a ha b hb hab
    obtain ⟨t₀, t₁, -, hq1, -, h1⟩ := hf a ha
    obtain ⟨u₀, u₁, hq0', -, h0', -⟩ := hf b hb
    have hu : t₁ < u₀ := by
      by_contra hle
      have := h1 u₀ (not_lt.1 hle)
      linarith
    calc (f a : ℝ) < t₁ := hq1
      _ < u₀ := by exact_mod_cast hu
      _ < f b := hq0'
  intro a ha b hb hfab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hlt a ha b hb h
    rw [hfab] at this
    exact lt_irrefl _ this
  · have := hlt b hb a ha h
    rw [hfab] at this
    exact lt_irrefl _ this

/-- **Pauses under dilation**: `t ↦ (√c)⁻¹ w(ct)` pauses at `a` iff `w` pauses at `√c · a`. -/
theorem isLevelPause_dilPath_iff {c : ℝ≥0} (hc : c ≠ 0) (a : ℝ) :
    IsLevelPause a (Sec7.Dilation.dilPath c w) ↔ IsLevelPause (√(c : ℝ) * a) w := by
  have hs : 0 < √(c : ℝ) := Real.sqrt_pos.2 (by positivity)
  have habs : ∀ t : ℝ≥0, |Sec7.Dilation.dilPath c w t| = (√(c : ℝ))⁻¹ * |w (c * t)| := fun t => by
    rw [Sec7.Dilation.dilPath, abs_mul, abs_of_pos (inv_pos.2 hs)]
  have hle : ∀ x y : ℝ, x ≤ (√(c : ℝ))⁻¹ * y ↔ √(c : ℝ) * x ≤ y := fun x y => by
    rw [← div_eq_inv_mul, le_div_iff₀ hs, mul_comm]
  have hge : ∀ x y : ℝ, (√(c : ℝ))⁻¹ * y ≤ x ↔ y ≤ √(c : ℝ) * x := fun x y => by
    rw [← div_eq_inv_mul, div_le_iff₀ hs, mul_comm]
  have hc0 : 0 < c := pos_iff_ne_zero.2 hc
  constructor
  · rintro ⟨t₀, t₁, h01, h0, h1⟩
    refine ⟨c * t₀, c * t₁, mul_lt_mul_of_pos_left h01 hc0, (hle _ _).1 (habs t₀ ▸ h0), fun s hs' => ?_⟩
    have e : c * (c⁻¹ * s) = s := mul_inv_cancel_left₀ hc s
    have := h1 (c⁻¹ * s) (by
      rw [← mul_le_mul_iff_of_pos_left hc0, e]
      exact hs')
    rw [habs, e] at this
    exact (hge _ _).1 this
  · rintro ⟨t₀, t₁, h01, h0, h1⟩
    have e : ∀ t, c * (c⁻¹ * t) = t := fun t => mul_inv_cancel_left₀ hc t
    refine ⟨c⁻¹ * t₀, c⁻¹ * t₁, mul_lt_mul_of_pos_left h01 (inv_pos.2 hc0), ?_, fun s hs' => ?_⟩
    · rw [habs, e]
      exact (hle _ _).2 h0
    · rw [habs]
      refine (hge _ _).2 (h1 _ ?_)
      calc c * s ≤ c * (c⁻¹ * t₁) := mul_le_mul_of_nonneg_left hs' c.2
        _ = t₁ := e t₁

/-- **Pauses of a continuous path are read from a dense set of times.** -/
theorem isLevelPause_iff_dense (hw : Continuous w) {D : Set ℝ≥0} (hD : Dense D) (a : ℝ) :
    IsLevelPause a w ↔ ∃ q₀ ∈ D, ∃ q₁ ∈ D, q₀ < q₁ ∧
      (∀ m : ℕ, ∃ s ∈ D, s ≤ q₀ ∧ a - 1 / ((m : ℝ) + 1) < |w s|) ∧ ∀ s ∈ D, s ≤ q₁ → |w s| ≤ a := by
  have hwa : Continuous fun t => |w t| := continuous_abs.comp hw
  constructor
  · rintro ⟨t₀, t₁, h01, h0, h1⟩
    obtain ⟨q₀, hq₀D, hq₀⟩ := hD.exists_between h01
    obtain ⟨q₁, hq₁D, hq₁⟩ := hD.exists_between hq₀.2
    refine ⟨q₀, hq₀D, q₁, hq₁D, hq₁.1, fun m => ?_, fun s _ hs => h1 s (hs.trans hq₁.2.le)⟩
    have hm : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hev : ∀ᶠ s in 𝓝 t₀, |w t₀| - 1 / ((m : ℝ) + 1) < |w s| :=
      (hwa.tendsto t₀).eventually (lt_mem_nhds (by linarith))
    obtain ⟨u, hu, hut⟩ := (Metric.eventually_nhds_iff.1 hev)
    -- a time of `D` in `(t₀, min (t₀ + δ) q₀)`
    have hlt : t₀ < min (t₀ + (u / 2).toNNReal) q₀ :=
      lt_min (lt_add_of_pos_right _ (Real.toNNReal_pos.2 (by linarith))) hq₀.1
    obtain ⟨s, hsD, hs⟩ := hD.exists_between hlt
    refine ⟨s, hsD, hs.2.le.trans (min_le_right _ _), ?_⟩
    have hdist : dist s t₀ < u := by
      rw [NNReal.dist_eq, abs_of_pos (sub_pos.2 (show (t₀ : ℝ) < s by exact_mod_cast hs.1))]
      have h2 : s < t₀ + (u / 2).toNNReal := hs.2.trans_le (min_le_left _ _)
      have h3 : (s : ℝ) < t₀ + u / 2 := by
        have := (NNReal.coe_lt_coe.2 h2)
        rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at this
        exact this
      linarith
    linarith [hut hdist]
  · rintro ⟨q₀, -, q₁, -, h01, h0, h1⟩
    -- the maximum of `|w|` on `[0, q₀]`
    obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := q₀)).exists_isMaxOn
      ⟨0, left_mem_Icc.2 zero_le⟩ hwa.continuousOn
    refine ⟨t₀, q₁, ht₀.2.trans_lt h01, ?_, fun s hs => ?_⟩
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨s, -, hsq, hs⟩ := h0 m
      have := hmax ⟨zero_le, hsq⟩
      simp only [mem_ofPred_eq] at this
      linarith
    · by_contra hlt
      rw [not_le] at hlt
      have hev : ∀ᶠ u in 𝓝 s, a < |w u| := (hwa.tendsto s).eventually (lt_mem_nhds hlt)
      rcases eq_or_lt_of_le hs with heq | hlt'
      · subst heq
        obtain ⟨d, hdD, hdlt, hd⟩ : ∃ d ∈ D, d < s ∧ a < |w d| := by
          obtain ⟨u, hu, hut⟩ := Metric.eventually_nhds_iff.1 hev
          have hlo : (s - (u / 2).toNNReal) < s := by
            refine tsub_lt_self ?_ (Real.toNNReal_pos.2 (by linarith))
            exact lt_of_le_of_lt zero_le h01
          obtain ⟨d, hdD, hd⟩ := hD.exists_between hlo
          refine ⟨d, hdD, hd.2, hut ?_⟩
          rw [NNReal.dist_eq, abs_of_neg (sub_neg.2 (show (d : ℝ) < s by exact_mod_cast hd.2))]
          have h2 := NNReal.coe_lt_coe.2 hd.1
          rw [NNReal.coe_sub_def, Real.coe_toNNReal _ (by linarith)] at h2
          linarith [le_max_left ((s : ℝ) - u / 2) 0]
        exact absurd (h1 d hdD hdlt.le) (not_le.2 hd)
      · obtain ⟨u, hu, hut⟩ := Metric.eventually_nhds_iff.1 hev
        have hlt2 : s < min (s + (u / 2).toNNReal) q₁ :=
          lt_min (lt_add_of_pos_right _ (Real.toNNReal_pos.2 (by linarith))) hlt'
        obtain ⟨d, hdD, hd⟩ := hD.exists_between hlt2
        have hdist : dist d s < u := by
          rw [NNReal.dist_eq, abs_of_pos (sub_pos.2 (show (s : ℝ) < d by exact_mod_cast hd.1))]
          have h2 : d < s + (u / 2).toNNReal := hd.2.trans_le (min_le_left _ _)
          have h3 : (d : ℝ) < s + u / 2 := by
            have := (NNReal.coe_lt_coe.2 h2)
            rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at this
            exact this
          linarith
        exact absurd (h1 d hdD (hd.2.le.trans (min_le_right _ _))) (not_le.2 (hut hdist))

end Pause

/-! ### The local stop of a continued path -/

section Stop

variable {r : ℝ} {w w' : ℝ≥0 → ℝ}

/-- **The local stop of a continuous path is read from a dense set of times.** -/
theorem localStopPath_top_lt_iff (hw : Continuous w) {D : Set ℝ≥0} (hD : Dense D) (t : ℝ≥0) :
    localStopPath r ⊤ w < t ↔ stopHorizon r < t ∨ ∃ d ∈ D, d < t ∧ r / 4 < |w d| := by
  rw [localStopPath, min_lt_iff, WithTop.coe_lt_coe,
    hitBelow_lt_iff (continuousOn_stopGap (r := r) hw.continuousOn) hD t]
  simp only [ENNReal.coe_lt_top, true_and, stopGap, sub_neg]

/-- **The local stop of a path that agrees with `w` through a local stop of `w` and does not pause at `r/4`.**
If `S = localStopPath r ζ w` with `S < ζ`, `w` continuous before `ζ`, `w 0 = 0`, `r > 0`, and `w'` is a path
equal to `w` on `[0, S]` that does not pause at level `r/4`, then `S` is also the local stop of `w'`. -/
theorem localStopPath_eq_of_not_isLevelPause (hr : 0 < r) {ζ : ℝ≥0∞} {S : ℝ≥0}
    (hwc : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hS : localStopPath r ζ w = S) (hSζ : (S : ℝ≥0∞) < ζ)
    (heq : ∀ s ≤ S, w' s = w s) (hpause : ¬ IsLevelPause (r / 4) w') :
    localStopPath r ⊤ w' = S := by
  have hr4 : 0 ≤ r := hr.le
  -- through `S`, `|w'| ≤ r/4`
  have hle : ∀ s ≤ S, |w' s| ≤ r / 4 := fun s hs => by
    rw [heq s hs]
    exact abs_le_of_le_localStopPath hwc hw0 hr4 (by rw [hS]; exact_mod_cast hs)
      (lt_of_le_of_lt (by exact_mod_cast hs) hSζ)
  -- `S ≤` the local stop of `w'`
  have hge : (S : WithTop ℝ≥0) ≤ localStopPath r ⊤ w' := by
    refine le_min (hS ▸ localStopPath_le_stopHorizon) (le_hitBelow fun s _ hs => ?_)
    by_contra hlt
    rw [not_le] at hlt
    have := hle s hlt.le
    simp only [stopGap] at hs
    linarith
  refine le_antisymm ?_ hge
  by_cases hH : (S : WithTop ℝ≥0) = stopHorizon r
  · rw [hH]; exact localStopPath_le_stopHorizon
  -- `S` is a hitting time of `w`: `|w S| ≥ r/4`
  have hhit : hitBelow (stopGap r w) ζ 0 = S := by
    have hmin : min (stopHorizon r : WithTop ℝ≥0) (hitBelow (stopGap r w) ζ 0) = S := hS
    rcases min_choice (stopHorizon r : WithTop ℝ≥0) (hitBelow (stopGap r w) ζ 0) with h | h
    · rw [h] at hmin; exact absurd hmin.symm hH
    · rw [h] at hmin; exact hmin
  have hwS : r / 4 ≤ |w' S| := by
    have := le_of_hitBelow_eq (continuousOn_stopGap (r := r) hwc) hhit
    rw [heq S le_rfl]
    simp only [stopGap] at this
    linarith
  -- otherwise `w'` pauses at `r/4` on `[S, t₁]`
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : (S : WithTop ℝ≥0) < hitBelow (stopGap r w') ⊤ 0 := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨t₁, hSt₁, ht₁⟩ : ∃ t₁ : ℝ≥0, S < t₁ ∧ (t₁ : WithTop ℝ≥0) < hitBelow (stopGap r w') ⊤ 0 := by
    induction h : hitBelow (stopGap r w') ⊤ 0 with
    | top => exact ⟨S + 1, lt_add_one S, WithTop.coe_lt_top _⟩
    | coe u =>
      rw [h] at hlt'
      have hSu : S < u := WithTop.coe_lt_coe.1 hlt'
      obtain ⟨t₁, h1, h2⟩ := exists_between hSu
      exact ⟨t₁, h1, WithTop.coe_lt_coe.2 h2⟩
  refine hpause ⟨S, t₁, hSt₁, hwS, fun s hs => ?_⟩
  by_contra hgt
  rw [not_le] at hgt
  have := hitBelow_le (f := stopGap r w') (ζ := ⊤) (ε := 0) (s := s) ENNReal.coe_lt_top
    (by simp only [stopGap]; linarith)
  exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt (WithTop.coe_le_coe.2 hs) ht₁)) (lt_irrefl _)

end Stop

/-! ### Codes -/

section Code

variable {nL nR : ℕ}

/-- The dyadic code space of a force word (the states at the dyadic times). -/
abbrev GCode (nL nR : ℕ) : Type := ℕ × ℕ → StateSp nL nR

/-- The driver code of a code. -/
def gDrv (c : GCode nL nR) : PCode := fun n k => (c (n, k)).1

/-- The code of the left mark `i`. -/
def gL (i : Fin nL) (c : GCode nL nR) : PCode := fun n k => (c (n, k)).2.1 i

/-- The code of the right mark `j`. -/
def gR (j : Fin nR) (c : GCode nL nR) : PCode := fun n k => (c (n, k)).2.2.1 j

theorem measurable_gDrv : Measurable (gDrv (nL := nL) (nR := nR)) :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => measurable_fst.comp (measurable_pi_apply (n, k))

theorem measurable_gL (i : Fin nL) : Measurable (gL (nR := nR) i) :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply (n, k))))

theorem measurable_gR (j : Fin nR) : Measurable (gR (nL := nL) j) :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    (measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_pi_apply (n, k)))))

/-- The codes whose driver is uniformly continuous on bounded dyadic sets (so the decoded driver is continuous). -/
def gUC : Set (GCode nL nR) := {c | ∀ N : ℕ, UC (gDrv c) N}

theorem measurableSet_gUC : MeasurableSet (gUC (nL := nL) (nR := nR)) := by
  have e : gUC (nL := nL) (nR := nR) = ⋂ N : ℕ, gDrv ⁻¹' {c : PCode | UC c N} := by
    ext c; simp [gUC]
  rw [e]
  exact MeasurableSet.iInter fun N => measurable_gDrv (measurableSet_UC N)

theorem continuous_dec_gDrv {c : GCode nL nR} (hc : c ∈ gUC) : Continuous (dec (gDrv c)) :=
  continuous_dec_of_uc hc

/-- A countable dense set of times. -/
def denseTimes : Set ℝ≥0 := (TopologicalSpace.exists_countable_dense ℝ≥0).choose

theorem countable_denseTimes : denseTimes.Countable := (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.1

theorem dense_denseTimes : Dense denseTimes := (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.2

theorem measurable_dec_gDrv_at (s : ℝ≥0) : Measurable fun c : GCode nL nR => dec (gDrv c) s :=
  measurable_dec.comp (measurable_gDrv.prodMk measurable_const)

/-- **The pause set**: the pairs (level, code) whose decoded driver is continuous and pauses at the level. -/
def pauseSet : Set (ℝ × GCode nL nR) := {p | p.2 ∈ gUC ∧ IsLevelPause p.1 (dec (gDrv p.2))}

/-- **The pause set is measurable** (in the level and the code jointly). -/
theorem measurableSet_pauseSet : MeasurableSet (pauseSet (nL := nL) (nR := nR)) := by
  set D := denseTimes
  have e : pauseSet (nL := nL) (nR := nR) = {p | p.2 ∈ gUC} ∩
      ⋃ q₀ ∈ D, ⋃ q₁ ∈ D, {p : ℝ × GCode nL nR | q₀ < q₁} ∩
        ((⋂ m : ℕ, ⋃ s ∈ D, {p : ℝ × GCode nL nR | s ≤ q₀ ∧ p.1 - 1 / ((m : ℝ) + 1) < |dec (gDrv p.2) s|}) ∩
          ⋂ s ∈ D, {p : ℝ × GCode nL nR | s ≤ q₁ → |dec (gDrv p.2) s| ≤ p.1}) := by
    ext p
    simp only [pauseSet, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter, exists_prop]
    constructor
    · rintro ⟨hc, hp⟩
      refine ⟨hc, ?_⟩
      obtain ⟨q₀, hq₀, q₁, hq₁, h01, h0, h1⟩ :=
        (isLevelPause_iff_dense (continuous_dec_gDrv hc) dense_denseTimes p.1).1 hp
      exact ⟨q₀, hq₀, q₁, hq₁, h01, fun m => by
        obtain ⟨s, hs, hsq, hlt⟩ := h0 m
        exact ⟨s, hs, hsq, hlt⟩, fun s hs => h1 s hs⟩
    · rintro ⟨hc, q₀, hq₀, q₁, hq₁, h01, h0, h1⟩
      refine ⟨hc, (isLevelPause_iff_dense (continuous_dec_gDrv hc) dense_denseTimes p.1).2
        ⟨q₀, hq₀, q₁, hq₁, h01, fun m => ?_, fun s hs => h1 s hs⟩⟩
      obtain ⟨s, hs, hsq, hlt⟩ := h0 m
      exact ⟨s, hs, hsq, hlt⟩
  rw [e]
  have hD : D.Countable := countable_denseTimes
  have hdec : ∀ s : ℝ≥0, Measurable fun p : ℝ × GCode nL nR => |dec (gDrv p.2) s| := fun s =>
    continuous_abs.measurable.comp ((measurable_dec_gDrv_at s).comp measurable_snd)
  refine (measurable_snd measurableSet_gUC).inter (MeasurableSet.biUnion hD fun q₀ _ =>
    MeasurableSet.biUnion hD fun q₁ _ => (MeasurableSet.const _).inter ((MeasurableSet.iInter fun m =>
      MeasurableSet.biUnion hD fun s _ => (MeasurableSet.const _).inter ?_).inter
      (MeasurableSet.biInter hD fun s _ => ?_)))
  · exact measurableSet_lt (measurable_fst.sub_const _) (hdec s)
  · by_cases hs : s ≤ q₁
    · simp only [hs, true_implies]
      exact measurableSet_le (hdec s) measurable_fst
    · simp only [hs, false_implies, ofPred_true, MeasurableSet.univ]

/-- **The local stop of radius `r` of the decoded driver** (`r²/64` off `gUC`). -/
def locStopCode (r : ℝ) (c : GCode nL nR) : WithTop ℝ≥0 :=
  open Classical in if c ∈ gUC then localStopPath r ⊤ (dec (gDrv c)) else stopHorizon r

theorem measurable_locStopCode (r : ℝ) : Measurable (locStopCode (nL := nL) (nR := nR) r) := by
  classical
  refine measurable_of_Iio fun t => ?_
  induction t with
  | top =>
    have e : locStopCode (nL := nL) (nR := nR) r ⁻¹' Iio ⊤ = univ := by
      ext c
      simp only [mem_preimage, mem_Iio, mem_univ, iff_true, locStopCode]
      split_ifs
      · exact lt_of_le_of_lt localStopPath_le_stopHorizon (WithTop.coe_lt_top _)
      · exact WithTop.coe_lt_top _
    rw [e]; exact MeasurableSet.univ
  | coe t =>
    have e : locStopCode (nL := nL) (nR := nR) r ⁻¹' Iio (t : WithTop ℝ≥0) =
        (gUC ∩ ({_c | stopHorizon r < t} ∪ ⋃ d ∈ denseTimes, {c | d < t ∧ r / 4 < |dec (gDrv c) d|})) ∪
          (gUCᶜ ∩ {_c | stopHorizon r < t}) := by
      ext c
      by_cases hc : c ∈ gUC
      · simp only [mem_preimage, mem_Iio, locStopCode, hc, ↓reduceIte, mem_union, mem_inter_iff, true_and,
          mem_ofPred_eq, mem_iUnion, exists_prop, mem_compl_iff, not_true_eq_false, false_and, or_false]
        exact localStopPath_top_lt_iff (continuous_dec_gDrv hc) dense_denseTimes t
      · simp only [mem_preimage, mem_Iio, locStopCode, hc, ↓reduceIte, WithTop.coe_lt_coe, mem_union,
          mem_inter_iff, false_and, mem_compl_iff, not_false_eq_true, true_and, mem_ofPred_eq, false_or]
    rw [e]
    refine (measurableSet_gUC.inter ((MeasurableSet.const _).union (MeasurableSet.biUnion countable_denseTimes
      fun d _ => (MeasurableSet.const _).inter (measurableSet_lt measurable_const
        (continuous_abs.measurable.comp (measurable_dec_gDrv_at d)))))).union
      (measurableSet_gUC.compl.inter (MeasurableSet.const _))

/-- The time `q ∧ τ` read as in `stopAt`. -/
theorem measurable_stopTime {α : Type*} [MeasurableSpace α] {τ : α → WithTop ℝ≥0} (hτ : Measurable τ) (q : ℝ≥0) :
    Measurable fun x => min q ((τ x).untopD q) :=
  measurable_const.min ((WithTop.measurable_untopD q).comp hτ)

/-- The value at a measurable time of a decoded code. -/
theorem measurable_dec_at {α : Type*} [MeasurableSpace α] {f : α → PCode} (hf : Measurable f) {T : α → ℝ≥0}
    (hT : Measurable T) : Measurable fun x => dec (f x) (T x) :=
  measurable_dec.comp (hf.prodMk hT)

/-- **The two-seed history read from a code** at the local stop of its decoded driver: the stop, and at the rational
times `q ∧ S` the driver and, on each side, the mark `iL` (resp. `jR`) if it is given, the driver otherwise. -/
def histOfCode (r : ℝ) (iL : Option (Fin nL)) (jR : Option (Fin nR)) (c : GCode nL nR) : TwoSeedHist :=
  (locStopCode r c, fun q =>
    (dec (gDrv c) (min (q : ℝ≥0) ((locStopCode r c).untopD q)),
      fun _ => match iL with
        | some i => dec (gL i c) (min (q : ℝ≥0) ((locStopCode r c).untopD q))
        | none => dec (gDrv c) (min (q : ℝ≥0) ((locStopCode r c).untopD q)),
      fun _ => match jR with
        | some j => dec (gR j c) (min (q : ℝ≥0) ((locStopCode r c).untopD q))
        | none => dec (gDrv c) (min (q : ℝ≥0) ((locStopCode r c).untopD q))))

theorem measurable_histOfCode (r : ℝ) (iL : Option (Fin nL)) (jR : Option (Fin nR)) :
    Measurable (histOfCode (nL := nL) (nR := nR) r iL jR) := by
  have hS := measurable_locStopCode (nL := nL) (nR := nR) r
  refine hS.prodMk (measurable_pi_iff.2 fun q => ?_)
  have hT := measurable_stopTime hS (q : ℝ≥0)
  refine (measurable_dec_at measurable_gDrv hT).prodMk ((measurable_pi_iff.2 fun _ => ?_).prodMk
    (measurable_pi_iff.2 fun _ => ?_))
  · cases iL with
    | some i => exact measurable_dec_at (measurable_gL i) hT
    | none => exact measurable_dec_at measurable_gDrv hT
  · cases jR with
    | some j => exact measurable_dec_at (measurable_gR j) hT
    | none => exact measurable_dec_at measurable_gDrv hT

end Code

end LocalExt

end InteractingSLE
