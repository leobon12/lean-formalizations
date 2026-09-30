import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# B5-V at a fixed time: the deterministic exhaustion step

Task B5V-FIX (`handoff/B5.md`, R1, step (e)). The coordinate-change rule for the boundary
measure (Sheffield, arXiv:1012.4797, proof of Thm 1.3 / Lemma 5.6, pp. 66–68; the window form is
`E1.ae_qBoundaryMeasureOn_revMap`) identifies `ν_{h⁰}` on each compact window `[u,v]` of the live
interval `(0₋(T), 0₋(t))` with `ν_{Y_t}` on `(F u, F v)`, `F = realRevMap V t`. This file does the
purely measure-theoretic exhaustion: from the window identities on rational windows, strict
monotonicity of `F` and its one-sided limits at the ends, the identity on the whole interval, and
on the closed interval when the endpoints carry no atoms.

* `measure_Ioo_eq_of_windows`: `νh (a,c) = νY (O,e)`;
* `measure_Icc_eq_of_windows`: `νh [a,c] = νY [O,e]` given no atoms at `a, c, O, e`.

Own elementary proof (continuity of measures along a countable directed family of windows).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace B5

/-- The rational windows of `(a,c)`. -/
def ratWin (a c : ℝ) : Type := {p : ℚ × ℚ // a < p.1 ∧ (p.1 : ℝ) < p.2 ∧ (p.2 : ℝ) < c}

instance (a c : ℝ) : Countable (ratWin a c) := by unfold ratWin; infer_instance

theorem iUnion_ratWin {a c : ℝ} :
    (⋃ p : ratWin a c, Ioo (p.1.1 : ℝ) p.1.2) = Ioo a c := by
  ext x
  simp only [mem_iUnion, mem_Ioo]
  constructor
  · rintro ⟨p, h1, h2⟩
    exact ⟨p.2.1.trans h1, h2.trans p.2.2.2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn h1
    obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn h2
    exact ⟨⟨(u, v), hu1, hu2.trans hv1, hv2⟩, hu2, hv1⟩

theorem directed_ratWin {a c : ℝ} {F : ℝ → ℝ} (hmono : StrictMonoOn F (Ioo a c)) :
    Directed (· ⊆ ·) (fun p : ratWin a c => Ioo (F p.1.1) (F p.1.2)) ∧
      Directed (· ⊆ ·) (fun p : ratWin a c => Ioo (p.1.1 : ℝ) p.1.2) := by
  have key : ∀ p q : ratWin a c, ∃ r : ratWin a c, (r.1.1 : ℝ) ≤ p.1.1 ∧ (r.1.1 : ℝ) ≤ q.1.1 ∧
      (p.1.2 : ℝ) ≤ r.1.2 ∧ (q.1.2 : ℝ) ≤ r.1.2 := by
    intro p q
    refine ⟨⟨(min p.1.1 q.1.1, max p.1.2 q.1.2), ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Rat.cast_min, Rat.cast_max, lt_min_iff, max_lt_iff, min_le_iff, le_max_iff,
        le_refl, true_or, or_true]
    · exact ⟨p.2.1, q.2.1⟩
    · exact (min_le_left _ _).trans_lt (p.2.2.1.trans_le (le_max_left _ _))
    · exact ⟨p.2.2.2, q.2.2.2⟩
  have mem : ∀ p : ratWin a c, (p.1.1 : ℝ) ∈ Ioo a c ∧ (p.1.2 : ℝ) ∈ Ioo a c := fun p =>
    ⟨⟨p.2.1, p.2.2.1.trans p.2.2.2⟩, ⟨p.2.1.trans p.2.2.1, p.2.2.2⟩⟩
  constructor
  · intro p q
    obtain ⟨r, h1, h2, h3, h4⟩ := key p q
    refine ⟨r, Ioo_subset_Ioo (hmono.monotoneOn (mem r).1 (mem p).1 h1)
        (hmono.monotoneOn (mem p).2 (mem r).2 h3),
      Ioo_subset_Ioo (hmono.monotoneOn (mem r).1 (mem q).1 h2)
        (hmono.monotoneOn (mem q).2 (mem r).2 h4)⟩
  · intro p q
    obtain ⟨r, h1, h2, h3, h4⟩ := key p q
    exact ⟨r, Ioo_subset_Ioo h1 h3, Ioo_subset_Ioo h2 h4⟩

/-- **Exhaustion of the open interval by windows.** -/
theorem measure_Ioo_eq_of_windows {νh νY : Measure ℝ} {F : ℝ → ℝ} {a c O e : ℝ}
    (hac : a < c) (hmono : StrictMonoOn F (Ioo a c))
    (hA : Tendsto F (𝓝[>] a) (𝓝 O)) (hC : Tendsto F (𝓝[<] c) (𝓝 e))
    (hwin : ∀ u v : ℚ, a < u → (u : ℝ) < v → (v : ℝ) < c →
      νh (Ioo u v) = νY (Ioo (F u) (F v))) :
    νh (Ioo a c) = νY (Ioo O e) := by
  -- `O < F x < e` on `(a,c)`
  have hlow : ∀ x ∈ Ioo a c, O < F x := by
    intro x hx
    set m := (a + x) / 2
    have hm : m ∈ Ioo a c := ⟨by simp only [m]; linarith [hx.1], by simp only [m]; linarith [hx.1, hx.2]⟩
    have hmx : m < x := by simp only [m]; linarith [hx.1]
    have hle : O ≤ F m := by
      refine le_of_tendsto hA ?_
      filter_upwards [Ioo_mem_nhdsGT hm.1] with y hy
      exact hmono.monotoneOn ⟨hy.1, hy.2.trans hm.2⟩ hm hy.2.le
    exact hle.trans_lt (hmono hm hx hmx)
  have hup : ∀ x ∈ Ioo a c, F x < e := by
    intro x hx
    set m := (x + c) / 2
    have hm : m ∈ Ioo a c := ⟨by simp only [m]; linarith [hx.1, hx.2], by simp only [m]; linarith [hx.2]⟩
    have hxm : x < m := by simp only [m]; linarith [hx.2]
    have hle : F m ≤ e := by
      refine ge_of_tendsto hC ?_
      filter_upwards [Ioo_mem_nhdsLT hm.2] with y hy
      exact hmono.monotoneOn hm ⟨hm.1.trans hy.1, hy.2⟩ hy.1.le
    exact (hmono hx hm hxm).trans_le hle
  have hUY : (⋃ p : ratWin a c, Ioo (F p.1.1) (F p.1.2)) = Ioo O e := by
    ext y
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨p, h1, h2⟩
      exact ⟨(hlow _ ⟨p.2.1, p.2.2.1.trans p.2.2.2⟩).trans h1,
        h2.trans (hup _ ⟨p.2.1.trans p.2.2.1, p.2.2.2⟩)⟩
    · rintro ⟨h1, h2⟩
      set m := (a + c) / 2
      have ham : a < m := by simp only [m]; linarith
      have hmc : m < c := by simp only [m]; linarith
      obtain ⟨u', hu', hsu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hA (Iio_mem_nhds h1))
      obtain ⟨v', hv', hsv⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hC (Ioi_mem_nhds h2))
      obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn (lt_min hu' ham)
      obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn (max_lt hv' hmc)
      have hum : (u : ℝ) < m := hu2.trans_le (min_le_right _ _)
      have hmv : m < v := (le_max_right _ _).trans_lt hv1
      refine ⟨⟨(u, v), hu1, hum.trans hmv, hv2⟩, ?_, ?_⟩
      · exact hsu ⟨hu1, hu2.trans_le (min_le_left _ _)⟩
      · exact hsv ⟨(le_max_left _ _).trans_lt hv1, hv2⟩
  obtain ⟨hdY, hdh⟩ := directed_ratWin hmono
  rw [← iUnion_ratWin, ← hUY, hdY.measure_iUnion, hdh.measure_iUnion]
  exact iSup_congr fun p => hwin _ _ p.2.1 p.2.2.1 p.2.2.2

/-- **Exhaustion, closed intervals.** -/
theorem measure_Icc_eq_of_windows {νh νY : Measure ℝ} {F : ℝ → ℝ} {a c O e : ℝ}
    (hac : a < c) (hmono : StrictMonoOn F (Ioo a c))
    (hA : Tendsto F (𝓝[>] a) (𝓝 O)) (hC : Tendsto F (𝓝[<] c) (𝓝 e))
    (hwin : ∀ u v : ℚ, a < u → (u : ℝ) < v → (v : ℝ) < c →
      νh (Ioo u v) = νY (Ioo (F u) (F v)))
    (ha : νh {a} = 0) (hc : νh {c} = 0) (hO : νY {O} = 0) (he : νY {e} = 0) :
    νh (Icc a c) = νY (Icc O e) := by
  rw [← measure_congr (Ioo_ae_eq_Icc' ha hc), ← measure_congr (Ioo_ae_eq_Icc' hO he)]
  exact measure_Ioo_eq_of_windows hac hmono hA hC hwin

end B5
end QuantumZipper
