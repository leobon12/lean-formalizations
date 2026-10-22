import HigherDimLQGMetric.Events.ShellCoverLocal
import HigherDimLQGMetric.Events.Defs

/-!
# Exponential failure bound at one grid point
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt roundLat)
open scoped ENNReal

variable {d : ℕ}

open Classical in
theorem shellCover_point_tail (hd : 1 ≤ d) {A p : ℝ} (hp1 : p < 1)
    (hp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ (z : Rd d) (r : ℕ → ℝ), (∀ i, 0 < r i) →
        (∀ i, r (i + 1) ≤ (1 / 64 : ℝ) * r i) →
      ∀ F : ℕ → Set Ω,
        (∀ i, AEEventIn P (fieldSigma0 h (ann z ((1 / 4) * r i) (8 * r i))) (F i)) →
        (∀ i, ENNReal.ofReal p ≤ P (F i)) →
        ∀ n : ℕ,
          P {ω | (((Finset.range n).filter (fun i => ω ∈ F i)).card : ℝ) <
            (1 / 2 : ℝ) * n} ≤ ENNReal.ofReal (Real.exp (-A * n)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (E : Rd d → ℝ → Set Ω) (hE : IsShellLocal P h E)
    (x : Rd d) (T : Finset ℤ) (hT : T.Nonempty)
    (hprob : ∀ j ∈ T, ∀ z : Rd d,
      ENNReal.ofReal p ≤ P (E z ((64 : ℝ) ^ j))) :
    P {ω | ∀ j ∈ T, ω ∉ E
      (latPt (((64 : ℝ) ^ j) / (100 * d))
        (roundLat (((64 : ℝ) ^ j) / (100 * d)) x)) ((64 : ℝ) ^ j)} ≤
      ENNReal.ofReal (Real.exp (-A * T.card)) := by
  classical
  let r : ℕ → ℝ := fun i => (64 : ℝ) ^ shellCoverIndex T hT i
  let z : ℕ → Rd d := fun i => latPt (r i / (100 * d)) (roundLat (r i / (100 * d)) x)
  let F : ℕ → Set Ω := fun i => if i < T.card then E (z i) (r i) else Set.univ
  have hr : ∀ i, 0 < r i := fun i => zpow_pos (by norm_num) _
  have hstep : ∀ i, r (i + 1) ≤ (1 / 64 : ℝ) * r i :=
    shellCoverIndex_zpow_step T hT
  have hloc : ∀ i, AEEventIn P
      (fieldSigma0 h (ann x ((1 / 4) * r i) (8 * r i))) (F i) := by
    intro i
    by_cases hi : i < T.card
    · simp only [F, ite_eq_left hi]
      obtain ⟨G, hG, hFG⟩ := hE (z i) (r i) (hr i)
      refine ⟨G, ?_, hFG⟩
      have heq : (1 / 4 : ℝ) * r i = r i / 4 := by ring
      rw [heq]
      exact (shellCover_fieldSigma0_mono h
        (shellCover_round_ann hd (hr i) x)) G hG
    · simp only [F, ite_eq_right hi]
      exact ⟨Set.univ, MeasurableSet.univ, Filter.EventuallyEq.rfl⟩
  have hmeas : ∀ i, ENNReal.ofReal p ≤ P (F i) := by
    intro i
    by_cases hi : i < T.card
    · simp only [F, ite_eq_left hi]
      exact hprob (shellCoverIndex T hT i) (shellCoverIndex_mem T hT hi) (z i)
    · simp only [F, ite_eq_right hi, measure_univ]
      simpa using (ENNReal.ofReal_le_ofReal hp1.le)
  have hn : 0 < T.card := Finset.card_pos.mpr hT
  have hsub : {ω : Ω | ∀ j ∈ T, ω ∉ E
      (latPt (((64 : ℝ) ^ j) / (100 * d))
        (roundLat (((64 : ℝ) ^ j) / (100 * d)) x)) ((64 : ℝ) ^ j)} ⊆
      {ω | (((Finset.range T.card).filter (fun i => ω ∈ F i)).card : ℝ) <
        (1 / 2 : ℝ) * T.card} := by
    intro ω hω
    have hzero : (Finset.range T.card).filter (fun i => ω ∈ F i) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hiiF
      have hii : i < T.card := Finset.mem_range.mp hi
      have hji := shellCoverIndex_mem T hT hii
      have hbad := hω (shellCoverIndex T hT i) hji
      exact hbad (by simpa only [F, ite_eq_left hii] using hiiF)
    change (((Finset.range T.card).filter (fun i => ω ∈ F i)).card : ℝ) <
      (1 / 2 : ℝ) * T.card
    rw [hzero]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_pos (by norm_num : (0 : ℝ) < 1 / 2) (by exact_mod_cast hn)
  exact (measure_mono hsub).trans (hp P h hh x r hr hstep F hloc hmeas T.card)

end HigherDimLQGMetric
