/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTimeMart

/-!
# The inverse strip clock along a path with an unbounded strip clock

Packet PROVE-ZHAN-A2. For an R36 strip path (`IsIntegratedSLEPath` of the chordal word `Strip.wordXL pL`, end mark
`v = V^{L, last}` started at `−1`) whose strip clock `t(s) = ∫₀ˢ (W − v)⁻²` is unbounded on the strip life
(`HasUnboundedStripClock`), the chordal time `s(t) = Strip.chordalTime` at strip time `t` (`chordT`) lies in the strip
life for **every** `t ≥ 0`, is the inverse of the strip clock, and is continuous, monotone and `0` at `0`. These are
the path facts behind the time change of `StripTimeLevy.lean`.

## Main results

* `chordT`, `clk` (the strip clock read at a chordal time in `ℝ≥0`);
* `isStripLife_chordT`, `clk_chordT` (`t(s(t)) = t`), `chordT_le_iff` (`s(t) ≤ s ↔ t ≤ t(s)` on the strip life),
  `le_chordT_iff`, `chordT_clk`, `monotone_chordT`, `continuous_chordT`, `chordT_zero`, `chordT_min`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ}

/-- The strip clock read at a chordal time. -/
def clk (w v : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ := Strip.stripClock (Strip.extPath w) (Strip.extPath v) s

/-- The chordal time at strip time `t` (the inverse strip clock). -/
def chordT (w v : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ≥0 :=
  (Strip.chordalTime (Strip.extPath w) (Strip.extPath v) t).toNNReal

section Path

variable {a : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  (hp : IsIntegratedSLEPath a (Strip.wordXL pL) xR ρL ρR w vL vR b ζ)
  (hcl : HasUnboundedStripClock w (vL (Fin.last nL)) ζ)
include hp hcl

/-- The inverse clock at `t` lies below a strip-life time `S` with `t ≤ t(S)`, and `t(s(t)) = t`. -/
theorem chordT_spec (t : ℝ≥0) : ∃ S : ℝ≥0, Strip.IsStripLife w (vL (Fin.last nL)) ζ S ∧
    chordT w (vL (Fin.last nL)) t ≤ S ∧ clk w (vL (Fin.last nL)) (chordT w (vL (Fin.last nL)) t) = t ∧
    (chordT w (vL (Fin.last nL)) t : ℝ) = Strip.chordalTime (Strip.extPath w)
      (Strip.extPath (vL (Fin.last nL))) t := by
  obtain ⟨S, hS, hTS⟩ := hcl t
  have hsep := Strip.isSepMark_of_isIntegratedSLEPath hp hS
  have ht : (t : ℝ) ∈ Icc 0 (Strip.stripClock (Strip.extPath w) (Strip.extPath (vL (Fin.last nL))) S) :=
    ⟨t.coe_nonneg, hTS⟩
  have hmem := hsep.chordalTime_mem ht
  have hc : (chordT w (vL (Fin.last nL)) t : ℝ) =
      Strip.chordalTime (Strip.extPath w) (Strip.extPath (vL (Fin.last nL))) t :=
    Real.coe_toNNReal _ hmem.1
  refine ⟨S, hS, ?_, ?_, hc⟩
  · rw [← NNReal.coe_le_coe, hc]; exact hmem.2
  · simp only [clk]; rw [hc]; exact hsep.stripClock_chordalTime ht

theorem isStripLife_chordT (t : ℝ≥0) :
    Strip.IsStripLife w (vL (Fin.last nL)) ζ (chordT w (vL (Fin.last nL)) t) := by
  obtain ⟨S, hS, hle, -⟩ := chordT_spec hp hcl t
  exact hS.mono hle

theorem clk_chordT (t : ℝ≥0) : clk w (vL (Fin.last nL)) (chordT w (vL (Fin.last nL)) t) = t := by
  obtain ⟨S, -, -, h, -⟩ := chordT_spec hp hcl t
  exact h

omit hcl in
/-- The strip clock is strictly increasing on the strip life. -/
theorem clk_lt_clk {s s' : ℝ≥0} (hs' : Strip.IsStripLife w (vL (Fin.last nL)) ζ s') (h : s < s') :
    clk w (vL (Fin.last nL)) s < clk w (vL (Fin.last nL)) s' := by
  have hsep := Strip.isSepMark_of_isIntegratedSLEPath hp hs'
  exact hsep.stripClock_lt ⟨s.coe_nonneg, by exact_mod_cast h.le⟩ ⟨s'.coe_nonneg, le_rfl⟩
    (by exact_mod_cast h)

omit hcl in
theorem clk_le_clk_iff {s s' : ℝ≥0} (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ s)
    (hs' : Strip.IsStripLife w (vL (Fin.last nL)) ζ s') :
    clk w (vL (Fin.last nL)) s ≤ clk w (vL (Fin.last nL)) s' ↔ s ≤ s' := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact absurd h (not_le.2 (clk_lt_clk hp hs hlt))
  · intro h
    rcases h.lt_or_eq with hlt | heq
    · exact (clk_lt_clk hp hs' hlt).le
    · rw [heq]

/-- `s(t) ≤ s ↔ t ≤ t(s)` for `s` in the strip life. -/
theorem chordT_le_iff {t s : ℝ≥0} (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ s) :
    chordT w (vL (Fin.last nL)) t ≤ s ↔ (t : ℝ) ≤ clk w (vL (Fin.last nL)) s := by
  rw [← clk_le_clk_iff hp (isStripLife_chordT hp hcl t) hs, clk_chordT hp hcl]

/-- `s ≤ s(t) ↔ t(s) ≤ t` for `s` in the strip life. -/
theorem le_chordT_iff {t s : ℝ≥0} (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ s) :
    s ≤ chordT w (vL (Fin.last nL)) t ↔ clk w (vL (Fin.last nL)) s ≤ t := by
  rw [← clk_le_clk_iff hp hs (isStripLife_chordT hp hcl t), clk_chordT hp hcl]

theorem chordT_clk {s : ℝ≥0} (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ s) :
    chordT w (vL (Fin.last nL)) (clk w (vL (Fin.last nL)) s).toNNReal = s := by
  have hsep := Strip.isSepMark_of_isIntegratedSLEPath hp hs
  have h0 : 0 ≤ clk w (vL (Fin.last nL)) s := hsep.stripClock_nonneg ⟨s.coe_nonneg, le_rfl⟩
  refine le_antisymm ?_ ?_
  · rw [chordT_le_iff hp hcl hs, Real.coe_toNNReal _ h0]
  · rw [le_chordT_iff hp hcl hs, Real.coe_toNNReal _ h0]

theorem monotone_chordT : Monotone (chordT w (vL (Fin.last nL))) := fun t t' h => by
  rw [chordT_le_iff hp hcl (isStripLife_chordT hp hcl t'), clk_chordT hp hcl]
  exact_mod_cast h

theorem chordT_zero : chordT w (vL (Fin.last nL)) 0 = 0 := by
  refine le_antisymm ?_ (zero_le (a := chordT w (vL (Fin.last nL)) 0))
  rw [chordT_le_iff hp hcl (Strip.IsStripLife.mono (isStripLife_chordT hp hcl 0)
    (zero_le (a := chordT w (vL (Fin.last nL)) 0)))]
  simp [clk, Strip.stripClock]

theorem continuous_chordT : Continuous (chordT w (vL (Fin.last nL))) := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  obtain ⟨S, hS, hTS⟩ := hcl (t₀ + 1)
  have hsep := Strip.isSepMark_of_isIntegratedSLEPath hp hS
  set c := Strip.stripClock (Strip.extPath w) (Strip.extPath (vL (Fin.last nL))) S with hc
  have hcont := hsep.continuousOn_chordalTime
  -- on `[0, t₀ + 1)` the inverse clock is `toNNReal` of a continuous function
  have hnhds : Iio (t₀ + 1) ∈ 𝓝 t₀ := Iio_mem_nhds (lt_add_one t₀)
  have hcomp : ContinuousOn (fun t : ℝ≥0 => (Strip.chordalTime (Strip.extPath w)
      (Strip.extPath (vL (Fin.last nL))) t).toNNReal) (Iio (t₀ + 1)) := by
    refine continuous_real_toNNReal.comp_continuousOn (hcont.comp NNReal.continuous_coe.continuousOn
      fun t ht => ⟨t.coe_nonneg, ?_⟩)
    have : (t : ℝ) < t₀ + 1 := by exact_mod_cast (mem_Iio.1 ht)
    linarith
  exact hcomp.continuousAt hnhds

/-- `s(t ∧ t(σ)) = s(t) ∧ σ` for `σ` in the strip life. -/
theorem chordT_min {σ : ℝ≥0} (hσ : Strip.IsStripLife w (vL (Fin.last nL)) ζ σ) (t : ℝ≥0) :
    chordT w (vL (Fin.last nL)) (min t (clk w (vL (Fin.last nL)) σ).toNNReal) =
      min (chordT w (vL (Fin.last nL)) t) σ := by
  have hsep := Strip.isSepMark_of_isIntegratedSLEPath hp hσ
  have h0 : 0 ≤ clk w (vL (Fin.last nL)) σ := hsep.stripClock_nonneg ⟨σ.coe_nonneg, le_rfl⟩
  rcases le_total (t : ℝ) (clk w (vL (Fin.last nL)) σ) with h | h
  · have h' : t ≤ (clk w (vL (Fin.last nL)) σ).toNNReal := Real.le_toNNReal_iff_coe_le h0 |>.2 h
    rw [min_eq_left h', min_eq_left ((chordT_le_iff hp hcl hσ).2 h)]
  · have h' : (clk w (vL (Fin.last nL)) σ).toNNReal ≤ t := by
      rw [Real.toNNReal_le_iff_le_coe]; exact h
    rw [min_eq_right h', chordT_clk hp hcl hσ, min_eq_right ((le_chordT_iff hp hcl hσ).2 h)]

end Path

end Zhan

end InteractingSLE
