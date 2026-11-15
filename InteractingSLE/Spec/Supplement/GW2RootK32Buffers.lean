/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootK32Separation
import InteractingSLE.Spec.Supplement.GW2RootJ31Launch

/-!
# Protection and exhaustion of J31's actual future buffers

Packet PROVE-T14-GW2ROOT2. The positive-level rule protects its CLOSED
stopped prefix. Its buffers increase, so the existing existential
exhaustion strengthens to eventual exhaustion of each compact interval.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootK32

open Exist StagedLaw Restart Supp8.GB6 Supp8.GB6.RelDrv.Version RootJ31 RootC24

/-- Before and at a closed-level entrance the continuous gauge is at
least its entrance level. This includes the deterministic cap endpoint. -/
theorem gaugeLevel_le_on_stop {g : ℝ≥0 → ℝ} (hg : Continuous g)
    {ε : ℝ} {c : ℝ≥0} (h0 : ε < g 0) {t : ℝ≥0}
    (ht : t ≤ gaugeStop g ε c) : ε ≤ g t := by
  by_contra hn
  have hgt : g t < ε := lt_of_not_ge hn
  obtain ⟨v, hv, he⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ t from bot_le)
    hg.continuousOn (show ε ∈ Icc (g t) (g 0) from ⟨hgt.le, h0.le⟩)
  have hvt : v < t := lt_of_le_of_ne hv.2 fun h => by
    rw [h] at he
    exact (ne_of_lt hgt) he
  have hs : gaugeStop g ε c ≤ v :=
    gaugeStop_le_of_le (hv.2.trans (ht.trans (gaugeStop_le _ _ _))) he.le
  exact (not_lt_of_ge ht) (hs.trans_lt hvt)

theorem monotone_localStop {g : ℝ≥0 → ℝ} (hg : Continuous g) :
    Monotone (localStop g) := by
  intro m m' hmm'
  have hlevel : gaugeLevel (g 0) m' ≤ gaugeLevel (g 0) m := by
    apply min_le_min le_rfl
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmm' 1)
  have hcap : (m + 1 : ℝ≥0) ≤ (m' + 1 : ℝ≥0) := by
    exact_mod_cast Nat.add_le_add_right hmm' 1
  by_cases ht : localStop g m' < (m + 1 : ℝ≥0)
  · exact gaugeStop_le_of_le ht.le
      ((gaugeStop_mem hg (ht.trans_le hcap)).trans hlevel)
  · exact (gaugeStop_le _ _ _).trans (le_of_not_gt ht)

theorem monotone_switchedBuffer (x : ℝ) (s v T b : ℝ≥0) (p : RecData × RecData) :
    Monotone (fun m => switchedBuffer x s v T b m p) := by
  intro m m' hmm'
  exact min_le_min le_rfl
    (monotone_localStop ((continuous_separationRead x s v p).comp
      (continuous_const.add continuous_id)) hmm')

/-- The actual separation level remains positive on the entire CLOSED
future buffer, including every old-prefix point used by that gauge. -/
theorem switchedBuffer_level_le (x : ℝ) (s v T b : ℝ≥0) (m : ℕ)
    (p : RecData × RecData) (hsep : 0 < RootJ31.separationRead x s v T p)
    {t : ℝ≥0} (ht : t ≤ switchedBuffer x s v T b m p) :
    gaugeLevel (RootJ31.separationRead x s v T p) m ≤
      RootJ31.separationRead x s v (T + t) p := by
  have hg : Continuous fun t : ℝ≥0 => RootJ31.separationRead x s v (T + t) p :=
    (continuous_separationRead x s v p).comp (continuous_const.add continuous_id)
  have hle : t ≤ localStop (fun t => RootJ31.separationRead x s v (T + t) p) m :=
    ht.trans (min_le_right _ _)
  have h := gaugeLevel_le_on_stop hg
    (gaugeLevel_lt (by simpa only [add_zero] using hsep) m) hle
  simpa only [add_zero] using h

/-- In particular, the absolute end of the buffer is strictly before
translated inversion contact, rather than merely at or before contact. -/
theorem switchedBuffer_lt_contact (x : ℝ) (s v T b : ℝ≥0) (m : ℕ)
    (p : RecData × RecData) (hsep : 0 < RootJ31.separationRead x s v T p) :
    ((T + switchedBuffer x s v T b m p : ℝ≥0) : ℝ≥0∞) < translatedContact x s v p :=
  (separationRead_pos_iff_lt_contact _ _ _ _ _).mp
    ((gaugeLevel_pos hsep m).trans_le (switchedBuffer_level_le _ _ _ _ _ _ _ hsep le_rfl))

/-- Every sufficiently large geometric buffer covers the chosen compact
future interval. This is the eventual form needed by the near comparison. -/
theorem eventually_lt_switchedBuffer (x : ℝ) (s v T b t : ℝ≥0)
    (p : RecData × RecData) (htb : t < b)
    (ht : ((T + t : ℝ≥0) : ℝ≥0∞) < translatedContact x s v p) :
    ∀ᶠ m in atTop, t < switchedBuffer x s v T b m p := by
  obtain ⟨m, hm⟩ := exists_lt_switchedBuffer x s v T b t p htb (by
    intro u hu
    exact (separationRead_pos_iff_lt_contact _ _ _ _ _).mpr
      ((ENNReal.coe_le_coe.mpr (add_le_add le_rfl hu)).trans_lt ht))
  exact eventually_atTop.mpr ⟨m, fun m' hmm' =>
    hm.trans_le (monotone_switchedBuffer x s v T b p hmm')⟩

theorem switchedBuffer_eq_zero_of_not_sep (x : ℝ) (s v T b : ℝ≥0) (m : ℕ)
    (p : RecData × RecData) (hsep : ¬0 < RootJ31.separationRead x s v T p) :
    switchedBuffer x s v T b m p = 0 := by
  have hz : RootJ31.separationRead x s v T p = 0 :=
    le_antisymm (le_of_not_gt hsep) (separationRead_nonneg _ _ _ _ _)
  have hl : gaugeLevel (RootJ31.separationRead x s v (T + 0) p) m = 0 := by
    simp only [add_zero, hz, gaugeLevel, zero_div, min_eq_left (by positivity :
      (0 : ℝ) ≤ 1 / ((m : ℝ) + 1))]
  have hs : localStop (fun t => RootJ31.separationRead x s v (T + t) p) m = 0 := by
    apply le_antisymm _ bot_le
    apply gaugeStop_le_of_le (t := 0) bot_le
    rw [hl, add_zero, hz]
  change min b (localStop (fun t => RootJ31.separationRead x s v (T + t) p) m) = 0
  rw [hs]
  exact le_antisymm (min_le_right b 0) bot_le

/-- The two geometric conditions for a positive switched buffer are exact. -/
theorem switchedBuffer_pos_iff (x : ℝ) (s v T b : ℝ≥0) (m : ℕ)
    (p : RecData × RecData) :
    0 < switchedBuffer x s v T b m p ↔
      0 < b ∧ 0 < RootJ31.separationRead x s v T p := by
  constructor
  · intro h
    refine ⟨h.trans_le (switchedBuffer_le _ _ _ _ _ _ _), ?_⟩
    by_contra hn
    rw [switchedBuffer_eq_zero_of_not_sep _ _ _ _ _ _ _ hn] at h
    exact (lt_irrefl 0) h
  · rintro ⟨hb, hsep⟩
    exact switchedBuffer_pos _ _ _ _ _ _ _ hb hsep

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The additional next-lifetime cap in D preserves geometric protection
even on exceptional branches, where the buffer is zero. -/
theorem sourceBuffer_le_switchedBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    sourceBuffer c r l a ω ≤ switchedBuffer (rootPt r.1) c.s
      (historyTime c r l + candidateCap c r a) (historyTime c r l)
      (candidateCap c r a) (candidateBuffer a) (futurePair c r l a ω) := by
  classical
  unfold sourceBuffer
  split_ifs
  · exact min_le_right _ _
  · exact bot_le

theorem sourceBuffer_lt_contact (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hsep : 0 < RootJ31.separationRead (rootPt r.1) c.s
      (historyTime c r l + candidateCap c r a) (historyTime c r l) (futurePair c r l a ω)) :
    ((historyTime c r l + sourceBuffer c r l a ω : ℝ≥0) : ℝ≥0∞) <
      translatedContact (rootPt r.1) c.s
        (historyTime c r l + candidateCap c r a) (futurePair c r l a ω) :=
  (ENNReal.coe_le_coe.mpr
    (add_le_add le_rfl (sourceBuffer_le_switchedBuffer c r l a ω))).trans_lt
      (switchedBuffer_lt_contact _ _ _ _ _ _ _ hsep)

/-- Positivity for D has exactly these four geometric/availability clauses.
In particular an alive gate alone does not supply the last two clauses. -/
theorem sourceBuffer_pos_iff (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    0 < sourceBuffer c r l a ω ↔
      ω ∈ RootCv.coverEvent c r ∧ oldSuccess c r l ω ∧
        0 < (nextRecord c r l a ω).2.1.toNNReal ∧
        0 < RootJ31.separationRead (rootPt r.1) c.s
          (historyTime c r l + candidateCap c r a) (historyTime c r l) (futurePair c r l a ω) := by
  classical
  constructor
  · intro h
    have hg : ω ∈ RootCv.coverEvent c r ∧ oldSuccess c r l ω := by
      by_contra hn
      change 0 < (if _ then _ else (0 : ℝ≥0)) at h
      rw [ite_eq_right hn] at h
      exact (lt_irrefl 0) h
    refine ⟨hg.1, hg.2, h.trans_le (sourceBuffer_le_next_time c r l a ω), ?_⟩
    exact ((switchedBuffer_pos_iff _ _ _ _ _ _ _).mp
      (h.trans_le (sourceBuffer_le_switchedBuffer c r l a ω))).2
  · rintro ⟨hcov, hold, hlife, hsep⟩
    exact sourceBuffer_pos c r l a ω hcov hold hlife hsep

end InteractingSLE.Theorem14.GW2TipSystem.RootK32
