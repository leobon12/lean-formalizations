/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RelDrv
import QuantumZipper.Proofs.Probability.Williams.MarkovHit

/-!
# Positive-distance localizations for GB6

The scalar gauge is positive before contact and vanishes at contact. Its first
passages below positive levels, capped at increasing deterministic times, give
positive stops strictly before contact and exhaust every compact live prefix.
The hitting time and closed-set entrance theorem are reused from Mathlib and
QuantumZipper. No probability law is used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.RelDrv.Version

/-- First passage below `ε`, capped at `c`. -/
def gaugeStop (g : ℝ≥0 → ℝ) (ε : ℝ) (c : ℝ≥0) : ℝ≥0 :=
  hittingBtwn (fun t (_ : Unit) => g t - ε) (Iic 0) 0 c ()

theorem gaugeStop_le (g : ℝ≥0 → ℝ) (ε : ℝ) (c : ℝ≥0) :
    gaugeStop g ε c ≤ c := hittingBtwn_le ()

theorem gaugeStop_le_of_le {g : ℝ≥0 → ℝ} {ε : ℝ} {c t : ℝ≥0}
    (ht : t ≤ c) (hg : g t ≤ ε) : gaugeStop g ε c ≤ t :=
  hittingBtwn_le_of_mem (zero_le : (0 : ℝ≥0) ≤ t) ht (sub_nonpos.2 hg)

theorem gaugeStop_mem {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} {c : ℝ≥0}
    (h : gaugeStop g ε c < c) : g (gaugeStop g ε c) ≤ ε := by
  have hex : ∃ t ∈ Icc (0 : ℝ≥0) c, g t - ε ∈ Iic (0 : ℝ) := by
    by_contra hn
    have he : gaugeStop g ε c = c := by
      simp only [gaugeStop, hittingBtwn, hn, ↓reduceIte]
    exact h.ne he
  have hm := QuantumZipper.Williams.mem_hittingBtwn_of_isClosed
    (u := fun t (_ : Unit) => g t - ε) (fun _ => hg.sub continuous_const) isClosed_Iic
    (ω := ()) hex
  exact sub_nonpos.1 hm

theorem gaugeStop_pos {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} {c : ℝ≥0}
    (hc : 0 < c) (h0 : ε < g 0) : 0 < gaugeStop g ε c := by
  by_contra hn
  have hz : gaugeStop g ε c = 0 := le_antisymm (not_lt.1 hn) zero_le
  have hm := gaugeStop_mem hg (hz ▸ hc)
  rw [hz] at hm
  exact (not_le.2 h0) hm

/-- The event of entrance before the cap is the event of a visit on the prefix. -/
theorem gaugeStop_le_iff {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} {c t : ℝ≥0}
    (ht : t < c) : gaugeStop g ε c ≤ t ↔ ∃ u ≤ t, g u ≤ ε := by
  constructor
  · intro h
    exact ⟨_, h, gaugeStop_mem hg (h.trans_lt ht)⟩
  · rintro ⟨u, hu, hgu⟩
    exact (gaugeStop_le_of_le (hu.trans ht.le) hgu).trans hu

/-- A finite contact at which the continuous gauge vanishes is strictly after
any positive-level localization. -/
theorem gaugeStop_lt_of_zero {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} {c T : ℝ≥0}
    (hε : 0 < ε) (h0 : ε < g 0) (hT : g T = 0) : gaugeStop g ε c < T := by
  obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ T from zero_le)
    hg.continuousOn (show ε / 2 ∈ Icc (g T) (g 0) by rw [hT]; constructor <;> linarith)
  have huT : u < T := lt_of_le_of_ne hu.2 fun he => by
    rw [he, hT] at hgu
    linarith only [hε, hgu]
  rcases le_total u c with huc | hcu
  · exact (gaugeStop_le_of_le huc (by linarith only [hgu, hε])).trans_lt huT
  · exact (gaugeStop_le g ε c).trans_lt (hcu.trans_lt huT)

/-- The threshold is at most half the starting gauge and tends to zero. -/
def gaugeLevel (g₀ : ℝ) (m : ℕ) : ℝ := min (g₀ / 2) (1 / ((m : ℝ) + 1))

theorem gaugeLevel_pos {g₀ : ℝ} (h0 : 0 < g₀) (m : ℕ) : 0 < gaugeLevel g₀ m :=
  lt_min (half_pos h0) (by positivity)

theorem gaugeLevel_lt {g₀ : ℝ} (h0 : 0 < g₀) (m : ℕ) : gaugeLevel g₀ m < g₀ :=
  (min_le_left _ _).trans_lt (half_lt_self h0)

/-- Positive-distance stops with increasing finite caps. -/
def localStop (g : ℝ≥0 → ℝ) (m : ℕ) : ℝ≥0 :=
  gaugeStop g (gaugeLevel (g 0) m) (m + 1)

theorem localStop_pos {g : ℝ≥0 → ℝ} (hg : Continuous g) (h0 : 0 < g 0) (m : ℕ) :
    0 < localStop g m := gaugeStop_pos hg (by positivity) (gaugeLevel_lt h0 m)

theorem localStop_lt {g : ℝ≥0 → ℝ} (hg : Continuous g) (h0 : 0 < g 0) {L : ℝ≥0∞}
    (hz : ∀ T : ℝ≥0, (T : ℝ≥0∞) = L → g T = 0) (m : ℕ) :
    (localStop g m : ℝ≥0∞) < L := by
  by_cases hL : L = ⊤
  · rw [hL]; exact ENNReal.coe_lt_top
  · lift L to ℝ≥0 using hL with T
    exact ENNReal.coe_lt_coe.2
      (gaugeStop_lt_of_zero hg (gaugeLevel_pos h0 m) (gaugeLevel_lt h0 m) (hz T rfl))

/-- Every compact interval on which the gauge is positive lies strictly before
one of the localizations. -/
theorem exists_lt_localStop {g : ℝ≥0 → ℝ} (hg : Continuous g) {t : ℝ≥0}
    (hp : ∀ u ≤ t, 0 < g u) : ∃ m : ℕ, t < localStop g m := by
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ≥0) t).Nonempty from ⟨0, zero_le, zero_le⟩) hg.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hp a ha.2)
  obtain ⟨k, hk⟩ := exists_nat_gt t
  let m := max n k
  have hcap : t < (m + 1 : ℝ≥0) := by
    have hkm : (k : ℝ≥0) ≤ m := by exact_mod_cast le_max_right n k
    exact hk.trans_le (hkm.trans (le_add_of_nonneg_right zero_le))
  have hlevel : gaugeLevel (g 0) m < g a := by
    refine (min_le_right _ _).trans_lt (lt_of_le_of_lt ?_ hn)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left n k) 1)
  refine ⟨m, ?_⟩
  by_contra hn
  have hstop : localStop g m ≤ t := not_lt.1 hn
  have hhit := gaugeStop_mem hg (hstop.trans_lt hcap)
  have hmin' : g a ≤ g (localStop g m) := hmin ⟨zero_le, hstop⟩
  exact (not_le.2 hlevel) (hmin'.trans hhit)

end InteractingSLE.Supp8.GB6.RelDrv.Version
