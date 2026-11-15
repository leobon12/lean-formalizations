/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalLoc
import InteractingSLE.Spec.Zhan.StripTimeClock

/-!
# Upper strip marks: the inverse strip clock of the innermost end mark

Packet PROVE-ZHAN-A33. PROVE-ZHAN-A2's inverse strip clock `Zhan.chordT w v` with `v = V^{L,0}`, the innermost left
mark started at `−1` (the strip end `−∞`), for a chordal path whose strip clock is unbounded on the strip life: it lies
in the strip life, inverts the clock, is monotone and continuous (the `*_up` lemmas; the proofs of
`StripTimeClock.lean`, with `Strip.isSepMark_of_isIntegratedSLEPath` replaced by `isSepMark_of_up`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan

variable {nL nR : ℕ}

/-- **The chordal word of upper strip marks**: the end mark `−1` (index `0`, the strip end `−∞`), then the chordal
images `−1 − e^{q_i}` of the upper strip boundary points `q_i + iπ` (indices `i.succ`). -/
def upWordXL (q : Fin nL → ℝ) : Fin (nL + 1) → ℝ := Fin.cons (-1) fun i => -1 - Real.exp (q i)

@[simp] theorem upWordXL_zero (q : Fin nL → ℝ) : upWordXL q 0 = -1 := by simp [upWordXL]

@[simp] theorem upWordXL_succ (q : Fin nL → ℝ) (i : Fin nL) : upWordXL q i.succ = -1 - Real.exp (q i) := by
  simp [upWordXL]

theorem upWordXL_succ_lt (q : Fin nL → ℝ) (i : Fin nL) : upWordXL q i.succ < upWordXL q 0 := by
  simp only [upWordXL_succ, upWordXL_zero]
  linarith [Real.exp_pos (q i)]

/-- **On the strip life the driver and the innermost end mark form a separated mark pair** (`Strip.IsSepMark`). -/
theorem isSepMark_of_up {a : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hx0 : xL 0 = -1) {s : ℝ≥0}
    (hs : Strip.IsStripLife w (vL 0) ζ s) :
    Strip.IsSepMark (Strip.extPath w) (Strip.extPath (vL 0)) s := by
  obtain ⟨-, -, -, hcw, hcvL, -, -, -, -, -, -, -, -, hvL, -⟩ := hp
  refine ⟨s.coe_nonneg, Strip.continuousOn_extPath hcw hs.1, Strip.continuousOn_extPath (hcvL _) hs.1,
    fun r hr => hs.2 _ (Real.toNNReal_le_iff_le_coe.2 hr.2), fun r hr => ?_⟩
  have hr' : (r.toNNReal : ℝ≥0∞) < ζ :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hs.1
  have h := hvL r.toNNReal hr' 0
  rw [hx0, Real.coe_toNNReal r hr.1] at h
  exact h


section Path

variable {a : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
  (hx0 : xL 0 = -1) (hcl : HasUnboundedStripClock w (vL 0) ζ)
include hp hx0 hcl

/-- The inverse clock at `t` lies below a strip-life time `S` with `t ≤ t(S)`, and `t(s(t)) = t`. -/
theorem chordT_spec_up (t : ℝ≥0) : ∃ S : ℝ≥0, Strip.IsStripLife w (vL 0) ζ S ∧
    chordT w (vL 0) t ≤ S ∧ clk w (vL 0) (chordT w (vL 0) t) = t ∧
    (chordT w (vL 0) t : ℝ) = Strip.chordalTime (Strip.extPath w)
      (Strip.extPath (vL 0)) t := by
  obtain ⟨S, hS, hTS⟩ := hcl t
  have hsep := isSepMark_of_up hp hx0 hS
  have ht : (t : ℝ) ∈ Icc 0 (Strip.stripClock (Strip.extPath w) (Strip.extPath (vL 0)) S) :=
    ⟨t.coe_nonneg, hTS⟩
  have hmem := hsep.chordalTime_mem ht
  have hc : (chordT w (vL 0) t : ℝ) =
      Strip.chordalTime (Strip.extPath w) (Strip.extPath (vL 0)) t :=
    Real.coe_toNNReal _ hmem.1
  refine ⟨S, hS, ?_, ?_, hc⟩
  · rw [← NNReal.coe_le_coe, hc]; exact hmem.2
  · simp only [clk]; rw [hc]; exact hsep.stripClock_chordalTime ht

theorem isStripLife_chordT_up (t : ℝ≥0) :
    Strip.IsStripLife w (vL 0) ζ (chordT w (vL 0) t) := by
  obtain ⟨S, hS, hle, -⟩ := chordT_spec_up hp hx0 hcl t
  exact hS.mono hle

theorem clk_chordT_up (t : ℝ≥0) : clk w (vL 0) (chordT w (vL 0) t) = t := by
  obtain ⟨S, -, -, h, -⟩ := chordT_spec_up hp hx0 hcl t
  exact h

omit hcl in
/-- The strip clock is strictly increasing on the strip life. -/
theorem clk_lt_clk_up {s s' : ℝ≥0} (hs' : Strip.IsStripLife w (vL 0) ζ s') (h : s < s') :
    clk w (vL 0) s < clk w (vL 0) s' := by
  have hsep := isSepMark_of_up hp hx0 hs'
  exact hsep.stripClock_lt ⟨s.coe_nonneg, by exact_mod_cast h.le⟩ ⟨s'.coe_nonneg, le_rfl⟩
    (by exact_mod_cast h)

omit hcl in
theorem clk_le_clk_iff_up {s s' : ℝ≥0} (hs : Strip.IsStripLife w (vL 0) ζ s)
    (hs' : Strip.IsStripLife w (vL 0) ζ s') :
    clk w (vL 0) s ≤ clk w (vL 0) s' ↔ s ≤ s' := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    exact absurd h (not_le.2 (clk_lt_clk_up hp hx0 hs hlt))
  · intro h
    rcases h.lt_or_eq with hlt | heq
    · exact (clk_lt_clk_up hp hx0 hs' hlt).le
    · rw [heq]

/-- `s(t) ≤ s ↔ t ≤ t(s)` for `s` in the strip life. -/
theorem chordT_le_iff_up {t s : ℝ≥0} (hs : Strip.IsStripLife w (vL 0) ζ s) :
    chordT w (vL 0) t ≤ s ↔ (t : ℝ) ≤ clk w (vL 0) s := by
  rw [← clk_le_clk_iff_up hp hx0 (isStripLife_chordT_up hp hx0 hcl t) hs, clk_chordT_up hp hx0 hcl]

/-- `s ≤ s(t) ↔ t(s) ≤ t` for `s` in the strip life. -/
theorem le_chordT_iff_up {t s : ℝ≥0} (hs : Strip.IsStripLife w (vL 0) ζ s) :
    s ≤ chordT w (vL 0) t ↔ clk w (vL 0) s ≤ t := by
  rw [← clk_le_clk_iff_up hp hx0 hs (isStripLife_chordT_up hp hx0 hcl t), clk_chordT_up hp hx0 hcl]

theorem chordT_clk_up {s : ℝ≥0} (hs : Strip.IsStripLife w (vL 0) ζ s) :
    chordT w (vL 0) (clk w (vL 0) s).toNNReal = s := by
  have hsep := isSepMark_of_up hp hx0 hs
  have h0 : 0 ≤ clk w (vL 0) s := hsep.stripClock_nonneg ⟨s.coe_nonneg, le_rfl⟩
  refine le_antisymm ?_ ?_
  · rw [chordT_le_iff_up hp hx0 hcl hs, Real.coe_toNNReal _ h0]
  · rw [le_chordT_iff_up hp hx0 hcl hs, Real.coe_toNNReal _ h0]

theorem monotone_chordT_up : Monotone (chordT w (vL 0)) := fun t t' h => by
  rw [chordT_le_iff_up hp hx0 hcl (isStripLife_chordT_up hp hx0 hcl t'), clk_chordT_up hp hx0 hcl]
  exact_mod_cast h

theorem chordT_zero_up : chordT w (vL 0) 0 = 0 := by
  refine le_antisymm ?_ (zero_le (a := chordT w (vL 0) 0))
  rw [chordT_le_iff_up hp hx0 hcl (Strip.IsStripLife.mono (isStripLife_chordT_up hp hx0 hcl 0)
    (zero_le (a := chordT w (vL 0) 0)))]
  simp [clk, Strip.stripClock]

theorem continuous_chordT_up : Continuous (chordT w (vL 0)) := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  obtain ⟨S, hS, hTS⟩ := hcl (t₀ + 1)
  have hsep := isSepMark_of_up hp hx0 hS
  set c := Strip.stripClock (Strip.extPath w) (Strip.extPath (vL 0)) S with hc
  have hcont := hsep.continuousOn_chordalTime
  -- on `[0, t₀ + 1)` the inverse clock is `toNNReal` of a continuous function
  have hnhds : Iio (t₀ + 1) ∈ 𝓝 t₀ := Iio_mem_nhds (lt_add_one t₀)
  have hcomp : ContinuousOn (fun t : ℝ≥0 => (Strip.chordalTime (Strip.extPath w)
      (Strip.extPath (vL 0)) t).toNNReal) (Iio (t₀ + 1)) := by
    refine continuous_real_toNNReal.comp_continuousOn (hcont.comp NNReal.continuous_coe.continuousOn
      fun t ht => ⟨t.coe_nonneg, ?_⟩)
    have : (t : ℝ) < t₀ + 1 := by exact_mod_cast (mem_Iio.1 ht)
    linarith
  exact hcomp.continuousAt hnhds

/-- `s(t ∧ t(σ)) = s(t) ∧ σ` for `σ` in the strip life. -/
theorem chordT_min_up {σ : ℝ≥0} (hσ : Strip.IsStripLife w (vL 0) ζ σ) (t : ℝ≥0) :
    chordT w (vL 0) (min t (clk w (vL 0) σ).toNNReal) =
      min (chordT w (vL 0) t) σ := by
  have hsep := isSepMark_of_up hp hx0 hσ
  have h0 : 0 ≤ clk w (vL 0) σ := hsep.stripClock_nonneg ⟨σ.coe_nonneg, le_rfl⟩
  rcases le_total (t : ℝ) (clk w (vL 0) σ) with h | h
  · have h' : t ≤ (clk w (vL 0) σ).toNNReal := Real.le_toNNReal_iff_coe_le h0 |>.2 h
    rw [min_eq_left h', min_eq_left ((chordT_le_iff_up hp hx0 hcl hσ).2 h)]
  · have h' : (clk w (vL 0) σ).toNNReal ≤ t := by
      rw [Real.toNNReal_le_iff_le_coe]; exact h
    rw [min_eq_right h', chordT_clk_up hp hx0 hcl hσ, min_eq_right ((le_chordT_iff_up hp hx0 hcl hσ).2 h)]

end Path

end InteractingSLE.ZhanGT4.UpMark
