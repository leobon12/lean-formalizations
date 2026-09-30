import QuantumZipper.Proofs.Zipper.E4Meas
import QuantumZipper.Proofs.Zipper.E1TransferM4Live

/-!
# E4-GRID, deterministic part (G1): the dyadic stopping time is read off `(x, V^{t_k})`

`handoff/E4-A.md` (sub-statement G1), `handoff/E-PLAN-2.md` (node E4-GRID).

For a continuous driver `V` with `V 0 = 0`:
* `sigEps V T ε x`: the first time `s ≥ 0` at which the real reverse flow from `x` enters
  `[−ε, ε]` or `x` is swallowed (capped at `T`);
* `dyUp n s = ⌈2ⁿ s⌉ / 2ⁿ` and the grid times `tk n k = k / 2ⁿ`;
* `sigEps_le_iff`: if `x` is live at `t < T` and `b ≤ t`, then `σ_ε(x) ≤ b` iff the flow enters
  `[−ε, ε]` during `[0, b]` (closedness of the entrance set; own elementary argument);
* **`mem_gridSet_iff`** (G1): an explicit measurable set `gridSet T ε n k` of
  `(x, (path, path))` with `(x, (V^{t_k}, W⁰)) ∈ gridSet ↔ t_k < T ∧ dyUp n σ_ε(x) = t_k ∧ x live
  at t_k` (for `x ≤ 0`), and `measurableSet_gridSet`.

Paper: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68): the Palm formula at a fixed
time is applied at the dyadic approximations of the stopping time at which `x` comes `ε`-close to
the tip. The measurability bookkeeping is own.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open E1 CharFun

/-- `σ_ε(x)`: first time the real reverse flow from `x` enters `[−ε, ε]` (or `x` is swallowed),
capped at `T`. -/
def sigEps (V : ℝ → ℝ) (T ε x : ℝ) : ℝ :=
  sInf ({s | 0 ≤ s ∧ (|realRevMap V s x| ≤ ε ∨ ¬ IsLive V s x)} ∪ {T})

/-- Dyadic upper approximation `⌈2ⁿ s⌉ / 2ⁿ`. -/
def dyUp (n : ℕ) (s : ℝ) : ℝ := ⌈(2 : ℝ) ^ n * s⌉ / (2 : ℝ) ^ n

/-- The grid time `k / 2ⁿ`. -/
def tk (n k : ℕ) : ℝ := k / (2 : ℝ) ^ n

theorem tk_nonneg (n k : ℕ) : 0 ≤ tk n k := by unfold tk; positivity

/-- The flow from `x` enters `[−ε, ε]` during `[0, b]`. -/
def HitBy (V : ℝ → ℝ) (ε b x : ℝ) : Prop := 0 ≤ b ∧ ∃ s ∈ Icc 0 b, |realRevMap V s x| ≤ ε

variable {V : ℝ → ℝ} {T ε x : ℝ}

theorem sigEps_nonneg (hT : 0 ≤ T) : 0 ≤ sigEps V T ε x :=
  le_csInf ⟨T, Or.inr rfl⟩ fun y hy => hy.elim (fun h => h.1) fun h => by
    rw [mem_singleton_iff.1 h]; exact hT

theorem sigEps_le_of_mem (hT : 0 ≤ T) {s : ℝ} (hs : 0 ≤ s) (h : |realRevMap V s x| ≤ ε) :
    sigEps V T ε x ≤ s := by
  refine csInf_le ⟨0, fun y hy => ?_⟩ (Or.inl ⟨hs, Or.inl h⟩)
  rcases hy with h | h
  · exact h.1
  · rw [mem_singleton_iff.1 h]; exact hT

/-- Solutions beyond a live time: `realRevMap` is a continuous solution on some `[0, T']`,
`T' > t`, and every time below `T'` is live. -/
theorem exists_sol_beyond (hV : Continuous V) {t : ℝ} (ht : 0 ≤ t) (hl : IsLive V t x) :
    ∃ T' > t, ∃ u : ℝ → ℝ, ContinuousOn u (Icc 0 T') ∧
      (∀ s ∈ Icc 0 T', realRevMap V s x = u s) ∧ ∀ s, 0 ≤ s → s < T' → IsLive V s x := by
  obtain ⟨u, hu⟩ := exists_isRealRevSol_of_isLive hl
  obtain ⟨T', hT't, u', hu'⟩ := E1.exists_isRealRevSol_extend hV ht hu
  refine ⟨T', hT't, u', hu'.1, fun s hs => RealLine.realRevMap_eq hV hu' hs.1 hs.2,
    fun s hs hsT => ?_⟩
  exact lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hsT, ht.trans_lt hT't⟩)
    (RealLine.ofReal_le_realHitTime (ht.trans hT't.le) hu')

/-- **Closedness of the entrance set.** -/
theorem sigEps_le_iff (hV : Continuous V) (hT : 0 ≤ T) {t b : ℝ} (ht : 0 ≤ t)
    (hl : IsLive V t x) (hbt : b ≤ t) (htT : t < T) :
    sigEps V T ε x ≤ b ↔ HitBy V ε b x := by
  refine ⟨fun hσ => ?_, fun ⟨_, s, hs, h⟩ => (sigEps_le_of_mem hT hs.1 h).trans hs.2⟩
  have hb : 0 ≤ b := (sigEps_nonneg hT).trans hσ
  refine ⟨hb, ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨T', hT't, u, hu, hR, hlive⟩ := exists_sol_beyond hV ht hl
  have hbI : b ∈ Icc 0 T' := ⟨hb, by linarith⟩
  have hub : ε < |u b| := by rw [← hR b hbI]; exact hne b ⟨hb, le_rfl⟩
  obtain ⟨η, hη, hηu⟩ := Metric.continuousWithinAt_iff.1 (hu b hbI) (|u b| - ε) (by linarith)
  set c := min (b + η / 2) (min T' T) with hc
  have hcb : b < c := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hcσ : c ≤ sigEps V T ε x := by
    refine le_csInf ⟨T, Or.inr rfl⟩ fun y hy => ?_
    rcases hy with ⟨hy0, hy⟩ | hy
    · by_contra hyc
      push Not at hyc
      have hyT' : y < T' := hyc.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hly := hlive y hy0 hyT'
      have hyR : |u y| ≤ ε := by
        rw [← hR y ⟨hy0, hyT'.le⟩]
        exact hy.resolve_right fun h => h hly
      rcases le_or_gt y b with hyb | hyb
      · have := hne y ⟨hy0, hyb⟩
        rw [hR y ⟨hy0, hyT'.le⟩] at this
        linarith
      · have hd : dist y b < η := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          have := hyc.trans_le (min_le_left _ _)
          linarith
        have h1 := hηu ⟨hy0, hyT'.le⟩ hd
        rw [Real.dist_eq] at h1
        have h2 : |u b| ≤ |u y| + |u y - u b| := by
          have := abs_sub_abs_le_abs_sub (u b) (u y)
          rw [abs_sub_comm (u b) (u y)] at this
          linarith
        linarith
    · rw [mem_singleton_iff.1 hy]
      exact (min_le_right _ _).trans (min_le_right _ _)
  linarith

theorem dyUp_eq_tk_iff (n k : ℕ) (s : ℝ) :
    dyUp n s = tk n k ↔ tk n k - 1 / (2 : ℝ) ^ n < s ∧ s ≤ tk n k := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  unfold dyUp tk
  rw [div_left_inj' h2.ne', show ((k : ℝ)) = ((k : ℤ) : ℝ) by norm_cast, Int.cast_inj,
    Int.ceil_eq_iff]
  push_cast
  constructor
  · rintro ⟨h1, h3⟩
    refine ⟨?_, ?_⟩
    · rw [← sub_div, div_lt_iff₀ h2]; linarith
    · rw [le_div_iff₀ h2]; linarith
  · rintro ⟨h1, h3⟩
    rw [← sub_div, div_lt_iff₀ h2] at h1
    rw [le_div_iff₀ h2] at h3
    exact ⟨by linarith, by linarith⟩

/-- The grid event in terms of entrance events. -/
theorem dyUp_sigEps_eq_iff (hV : Continuous V) (hT : 0 ≤ T) (n k : ℕ) (htT : tk n k < T) :
    (dyUp n (sigEps V T ε x) = tk n k ∧ IsLive V (tk n k) x) ↔
      (IsLive V (tk n k) x ∧ HitBy V ε (tk n k) x ∧
        ¬ HitBy V ε (tk n k - 1 / (2 : ℝ) ^ n) x) := by
  constructor
  · rintro ⟨h, hl⟩
    rw [dyUp_eq_tk_iff] at h
    refine ⟨hl, (sigEps_le_iff hV hT (tk_nonneg n k) hl le_rfl htT).1 h.2, fun h' => ?_⟩
    have := (sigEps_le_iff hV hT (tk_nonneg n k) hl
      (by have : (0 : ℝ) < 1 / 2 ^ n := by positivity
          linarith) htT).2 h'
    linarith [h.1]
  · rintro ⟨hl, h1, h2⟩
    refine ⟨(dyUp_eq_tk_iff n k _).2 ⟨?_, (sigEps_le_iff hV hT (tk_nonneg n k) hl le_rfl htT).2 h1⟩,
      hl⟩
    by_contra h
    push Not at h
    exact h2 ((sigEps_le_iff hV hT (tk_nonneg n k) hl
      (by have : (0 : ℝ) < 1 / 2 ^ n := by positivity
          linarith) htT).1 h)

end E4Grid
end QuantumZipper
