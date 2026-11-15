/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtCReindex

/-!
# Recorded histories at a restart: the current state, values at real times, concatenation, (R3) jointly measurable

Packet PROVE-LOCEXT-E ((R3) at a restart, PROVE-LOCEXT-C handoff, "What is missing" item 2). A recorded history
`y = (τ, (y_q)_{q ∈ ℚ≥0}) : DrivingHist nL nR` stores the stopped state `X_{q ∧ τ}` at the rational times. At a restart
at `τ` the history after `τ` is recorded in **restarted** rational time; turning it back into original rational time
needs the state at the real times `q − τ`, which are read off the rational samples by continuity.

* `histState y = y_{⌈τ⌉}`: the current state `X_τ` of a history stopped at a finite `τ` (`histState_stoppedHistory`);
* `upDyad n s = ⌈2ⁿ s⌉ / 2ⁿ`: dyadic rationals decreasing to `s`; `valueAt y s`: the coordinatewise `limsup` of
  `y_{upDyad n s}`, equal to the limit when it exists (`valueAt_eq_of_tendsto`); jointly measurable;
* `shiftState w x`: every coordinate translated by `w` (back from the frame centred at the driver);
* `concatHist y y'`: the history stopped at `τ + τ'` from the history `y` stopped at `τ` and the restarted history
  `y'` stopped at `τ'` (`measurable_concatHist`);
* `sampleFlow` and `reindexHist` are jointly measurable in the initial positions (`measurable_sampleFlow_pos`,
  **`measurable_reindexHist_pos`**): at a restart the positions of the distant marks are random.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7

variable {nL nR : ℕ}

/-! ### The current state of a recorded history -/

section HistState

/-- **The current state of a recorded history**: the value at the rational time `⌈τ⌉ ≥ τ`, which is `X_τ` when the
history is stopped at a finite `τ`. -/
def histState (y : DrivingHist nL nR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  y.2 ((⌈y.1.untopD 0⌉₊ : ℕ) : ℚ≥0)

/-- Evaluation of a recorded history at the rational `k / 2ⁿ`, jointly measurable in the history and `k`. -/
theorem measurable_eval_nat_div (n : ℕ) :
    Measurable fun p : DrivingHist nL nR × ℕ => p.1.2 ((p.2 : ℚ≥0) / 2 ^ n) :=
  measurable_from_prod_countable_left fun k =>
    (measurable_pi_apply ((k : ℚ≥0) / 2 ^ n)).comp (measurable_snd (α := WithTop ℝ≥0))

theorem measurable_histState : Measurable (histState (nL := nL) (nR := nR)) := by
  have hc : Measurable fun y : DrivingHist nL nR => ⌈y.1.untopD 0⌉₊ :=
    ((WithTop.measurable_untopD _).comp measurable_fst).nat_ceil
  have hev := measurable_eval_nat_div (nL := nL) (nR := nR) 0
  have e : histState (nL := nL) (nR := nR) =
      (fun p : DrivingHist nL nR × ℕ => p.1.2 ((p.2 : ℚ≥0) / 2 ^ 0)) ∘ fun y => (y, ⌈y.1.untopD 0⌉₊) := by
    funext y
    simp only [histState, Function.comp_apply, pow_zero, div_one]
  rw [e]
  exact hev.comp (measurable_id.prodMk hc)

/-- The current state of a history stopped at a finite time `T` is the state at `T`. -/
theorem histState_stoppedHistory {Ω : Type*} (X : ℝ≥0 → Ω → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} {T : ℝ≥0} (hT : τ ω = T) :
    histState (stoppedHistory X τ ω) = X T ω := by
  have hle : T ≤ ((⌈T⌉₊ : ℕ) : ℝ≥0) := Nat.le_ceil T
  simp only [histState, stoppedHistory, hT, WithTop.untopD_coe, stopAt_of_eq_coe hT]
  congr 1
  push_cast
  exact min_eq_right hle

end HistState

/-! ### Values at real times from rational samples -/

section ValueAt

/-- The index `⌈2ⁿ s⌉` of the dyadic rational `upDyad n s`. -/
def upIdx (n : ℕ) (s : ℝ≥0) : ℕ := ⌈2 ^ n * s⌉₊

theorem measurable_upIdx (n : ℕ) : Measurable (upIdx n) :=
  (measurable_const.mul measurable_id).nat_ceil

/-- The dyadic rational `⌈2ⁿ s⌉ / 2ⁿ ≥ s`. -/
def upDyad (n : ℕ) (s : ℝ≥0) : ℚ≥0 := ((upIdx n s : ℕ) : ℚ≥0) / 2 ^ n

theorem coe_upDyad (n : ℕ) (s : ℝ≥0) : ((upDyad n s : ℚ≥0) : ℝ≥0) = ((⌈2 ^ n * s⌉₊ : ℕ) : ℝ≥0) / 2 ^ n := by
  simp only [upDyad, upIdx]
  push_cast
  rfl

theorem le_upDyad (n : ℕ) (s : ℝ≥0) : s ≤ ((upDyad n s : ℚ≥0) : ℝ≥0) := by
  rw [coe_upDyad, le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

theorem upDyad_le (n : ℕ) (s : ℝ≥0) : ((upDyad n s : ℚ≥0) : ℝ≥0) ≤ s + 1 / 2 ^ n := by
  rw [coe_upDyad, div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity), mul_comm]
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem tendsto_upDyad (s : ℝ≥0) : Tendsto (fun n => ((upDyad n s : ℚ≥0) : ℝ≥0)) atTop (𝓝 s) := by
  have h1 : Tendsto (fun n : ℕ => s + 1 / 2 ^ n) atTop (𝓝 (s + 0)) := by
    refine tendsto_const_nhds.add ?_
    have h := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / 2) (by norm_num)
    refine h.congr fun n => ?_
    rw [one_div_pow]
  rw [add_zero] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (le_upDyad · s) (upDyad_le · s)

/-- **The value of a recorded history at a real time `s`**, read from its rational samples at the dyadic rationals
decreasing to `s` (coordinatewise `limsup`). -/
def valueAt (y : DrivingHist nL nR) (s : ℝ≥0) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (limsup (fun n => (y.2 (upDyad n s)).1) atTop,
    fun i => limsup (fun n => (y.2 (upDyad n s)).2.1 i) atTop,
    fun j => limsup (fun n => (y.2 (upDyad n s)).2.2 j) atTop)

theorem measurable_valueAt :
    Measurable fun p : DrivingHist nL nR × ℝ≥0 => valueAt p.1 p.2 := by
  have hs : ∀ n, Measurable fun p : DrivingHist nL nR × ℝ≥0 => p.1.2 (upDyad n p.2) := by
    intro n
    have e : (fun p : DrivingHist nL nR × ℝ≥0 => p.1.2 (upDyad n p.2)) =
        (fun p : DrivingHist nL nR × ℕ => p.1.2 ((p.2 : ℚ≥0) / 2 ^ n)) ∘ fun p => (p.1, upIdx n p.2) := rfl
    rw [e]
    exact (measurable_eval_nat_div n).comp (measurable_fst.prodMk ((measurable_upIdx n).comp measurable_snd))
  refine (Measurable.limsup fun n => (hs n).fst).prodMk
    ((Measurable.of_eval fun i => Measurable.limsup fun n => ?_).prodMk
      (Measurable.of_eval fun j => Measurable.limsup fun n => ?_))
  · exact (measurable_pi_apply i).comp (hs n).snd.fst
  · exact (measurable_pi_apply j).comp (hs n).snd.snd

/-- If the samples at the dyadic rationals decreasing to `s` converge, `valueAt` is their limit. -/
theorem valueAt_eq_of_tendsto {y : DrivingHist nL nR} {s : ℝ≥0} {v : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (h : Tendsto (fun n => y.2 (upDyad n s)) atTop (𝓝 v)) : valueAt y s = v := by
  have h1 : Tendsto (fun n => (y.2 (upDyad n s)).1) atTop (𝓝 v.1) := (continuous_fst.tendsto _).comp h
  have h2 : Tendsto (fun n => (y.2 (upDyad n s)).2) atTop (𝓝 v.2) := (continuous_snd.tendsto _).comp h
  have h2L : Tendsto (fun n => (y.2 (upDyad n s)).2.1) atTop (𝓝 v.2.1) := (continuous_fst.tendsto _).comp h2
  have h2R : Tendsto (fun n => (y.2 (upDyad n s)).2.2) atTop (𝓝 v.2.2) := (continuous_snd.tendsto _).comp h2
  refine Prod.ext h1.limsup_eq (Prod.ext (funext fun i => ?_) (funext fun j => ?_))
  · exact ((continuous_apply i).tendsto _ |>.comp h2L).limsup_eq
  · exact ((continuous_apply j).tendsto _ |>.comp h2R).limsup_eq

end ValueAt

/-! ### Concatenation of a history and a restarted history -/

section Concat

/-- Every coordinate of a state translated by `w` (from the frame centred at the driver back to the original one). -/
def shiftState (w : ℝ) (x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (x.1 + w, fun i => x.2.1 i + w, fun j => x.2.2 j + w)

theorem measurable_shiftState : Measurable fun p : ℝ × (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) => shiftState p.1 p.2 := by
  refine (measurable_snd.fst.add measurable_fst).prodMk
    ((Measurable.of_eval fun i => ?_).prodMk (Measurable.of_eval fun j => ?_))
  · exact ((measurable_pi_apply i).comp measurable_snd.snd.fst).add measurable_fst
  · exact ((measurable_pi_apply j).comp measurable_snd.snd.snd).add measurable_fst

/-- The value of the concatenated history at the rational time `q`. -/
def concatAt (q : ℚ≥0) (p : DrivingHist nL nR × DrivingHist nL nR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  if (q : ℝ≥0) ≤ p.1.1.untopD 0 then p.1.2 q
  else shiftState (histState p.1).1 (valueAt p.2 ((q : ℝ≥0) - p.1.1.untopD 0))

/-- **The concatenated history**: from a history `y` stopped at a finite `τ` and a restarted history `y'` (centred at
the driver at `τ`, in restarted time) stopped at a finite `τ'`, the history stopped at `τ + τ'`: at a rational
`q ≤ τ` the value of `y`, at `q > τ` the value of `y'` at the real time `q − τ`, translated back by the driver
`W_τ`. -/
def concatHist (y y' : DrivingHist nL nR) : DrivingHist nL nR :=
  (((y.1.untopD 0 + y'.1.untopD 0 : ℝ≥0) : WithTop ℝ≥0), fun q => concatAt q (y, y'))

theorem measurable_concatAt (q : ℚ≥0) : Measurable (concatAt (nL := nL) (nR := nR) q) := by
  have hτ : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => p.1.1.untopD 0 :=
    (WithTop.measurable_untopD _).comp measurable_fst.fst
  have h1 : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => p.1.2 q :=
    (measurable_pi_apply q).comp measurable_fst.snd
  have hv0 : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => (p.2, (q : ℝ≥0) - p.1.1.untopD 0) :=
    measurable_snd.prodMk (measurable_const.sub hτ)
  have hv : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => valueAt p.2 ((q : ℝ≥0) - p.1.1.untopD 0) := by
    have h := measurable_valueAt.comp hv0
    exact h
  have hw : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => (histState p.1).1 :=
    (measurable_histState.comp measurable_fst).fst
  have h2 : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR =>
      shiftState (histState p.1).1 (valueAt p.2 ((q : ℝ≥0) - p.1.1.untopD 0)) := by
    have h := measurable_shiftState.comp (hw.prodMk hv)
    exact h
  have hs : MeasurableSet {p : DrivingHist nL nR × DrivingHist nL nR | (q : ℝ≥0) ≤ p.1.1.untopD 0} :=
    measurableSet_le measurable_const hτ
  unfold concatAt
  exact Measurable.ite hs h1 h2

theorem concatHist_snd (y y' : DrivingHist nL nR) (q : ℚ≥0) : (concatHist y y').2 q = concatAt q (y, y') := rfl

theorem measurable_concatHist :
    Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => concatHist p.1 p.2 := by
  have hτ : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => p.1.1.untopD 0 :=
    (WithTop.measurable_untopD _).comp measurable_fst.fst
  have hτ' : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => p.2.1.untopD 0 :=
    (WithTop.measurable_untopD _).comp measurable_snd.fst
  have h1 : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR =>
      (((p.1.1.untopD 0 + p.2.1.untopD 0 : ℝ≥0) : WithTop ℝ≥0)) := WithTop.measurable_coe.comp (hτ.add hτ')
  have h2 : Measurable fun p : DrivingHist nL nR × DrivingHist nL nR => fun q : ℚ≥0 => concatAt q p :=
    Measurable.of_eval fun q => measurable_concatAt q
  exact h1.prodMk h2

end Concat

/-! ### (R3) jointly measurable in the positions -/

section Positions

theorem measurable_eulerSeq_pos {F : ℝ → ℝ} (hF : Measurable F) (h : ℝ) (n : ℕ) :
    ∀ k : ℕ, Measurable fun p : ℝ × (ℚ≥0 → ℝ) => Sec2.eulerSeq F p.1 h (fun j => p.2 ((j : ℚ≥0) / 2 ^ n)) k
  | 0 => measurable_fst
  | k + 1 => by
    have ih := measurable_eulerSeq_pos hF h n k
    have hw : Measurable fun p : ℝ × (ℚ≥0 → ℝ) => p.2 ((k : ℚ≥0) / 2 ^ n) :=
      (measurable_pi_apply _).comp measurable_snd
    exact ih.add (measurable_const.mul (hF.comp (ih.sub hw)))

theorem measurable_sampleEuler_pos {F : ℝ → ℝ} (hF : Measurable F) (n : ℕ) :
    Measurable fun p : ℝ × (ℚ≥0 → ℝ) × ℝ => sampleEuler F p.1 n p.2.1 p.2.2 := by
  have hE : Measurable fun q : (ℝ × (ℚ≥0 → ℝ)) × ℕ =>
      Sec2.eulerSeq F q.1.1 (1 / 2 ^ n) (fun j => q.1.2 ((j : ℚ≥0) / 2 ^ n)) q.2 :=
    measurable_from_prod_countable_left fun k => measurable_eulerSeq_pos hF _ n k
  have hw : Measurable fun q : (ℝ × (ℚ≥0 → ℝ)) × ℕ => q.1.2 ((q.2 : ℚ≥0) / 2 ^ n) :=
    measurable_from_prod_countable_left fun k =>
      (measurable_pi_apply ((k : ℚ≥0) / 2 ^ n)).comp (measurable_snd (α := ℝ) (β := ℚ≥0 → ℝ))
  have hk : Measurable fun p : ℝ × (ℚ≥0 → ℝ) × ℝ => ((p.1, p.2.1), Girsanov.stepIdx n p.2.2) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk ((Girsanov.measurable_stepIdx n).comp measurable_snd.snd)
  have hg : Measurable fun p : ℝ × (ℚ≥0 → ℝ) × ℝ => ((Girsanov.grid n (Girsanov.stepIdx n p.2.2) : ℝ≥0) : ℝ) := by
    have : Measurable fun k : ℕ => ((Girsanov.grid n k : ℝ≥0) : ℝ) := measurable_from_nat
    exact this.comp ((Girsanov.measurable_stepIdx n).comp measurable_snd.snd)
  unfold sampleEuler Sec2.eulerAt
  exact (hE.comp hk).add ((measurable_snd.snd.sub hg).mul (hF.comp ((hE.comp hk).sub (hw.comp hk))))

/-- `sampleFlow` is jointly measurable in the initial position, the samples and the time. -/
theorem measurable_sampleFlow_pos {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable fun p : ℝ × (ℚ≥0 → ℝ) × ℝ => sampleFlow F p.1 p.2.1 p.2.2 :=
  Measurable.limsup fun n => measurable_sampleEuler_pos hF n

/-- **The re-indexing map of (R3) is jointly measurable in the positions and the two-seed history** (at a restart
the positions `V_τ − W_τ` of the marks are random). -/
theorem measurable_reindexHist_pos {r : ℝ} (hr : 0 < r) :
    Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × TwoSeedHist => reindexHist p.1.1 p.1.2 r p.2 := by
  classical
  unfold reindexHist
  refine measurable_snd.fst.prodMk (Measurable.of_eval fun q => ?_)
  have hq : ∀ q' : ℚ≥0, Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × TwoSeedHist => p.2.2 q' := fun q' =>
    (measurable_pi_apply q').comp measurable_snd.snd
  have hx : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × TwoSeedHist => fun q' : ℚ≥0 => (p.2.2 q').1 :=
    Measurable.of_eval fun q' => (hq q').fst
  have ht : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × TwoSeedHist =>
      ((min (q : ℝ≥0) (p.2.1.untopD q) : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp ((measurable_const.min (WithTop.measurable_untopD _)).comp measurable_snd.fst)
  refine (hq q).fst.prodMk ((Measurable.of_eval fun i => ?_).prodMk (Measurable.of_eval fun j => ?_))
  · have hxi : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × TwoSeedHist => p.1.1 i :=
      (measurable_pi_apply i).comp measurable_fst.fst
    refine Measurable.ite (measurableSet_eq_fun hxi measurable_const)
      ((measurable_pi_apply 0).comp (hq q).snd.fst) ?_
    have hF : Measurable (Sec2.leftMarkDrift r) := (Sec2.lipschitzWith_leftMarkDrift hr).continuous.measurable
    have h2 := (measurable_sampleFlow_pos hF).comp (hxi.prodMk (hx.prodMk ht))
    exact h2
  · have hxj : Measurable fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × TwoSeedHist => p.1.2 j :=
      (measurable_pi_apply j).comp measurable_fst.snd
    refine Measurable.ite (measurableSet_eq_fun hxj measurable_const)
      ((measurable_pi_apply 0).comp (hq q).snd.snd) ?_
    have hF : Measurable (Sec2.rightMarkDrift r) := (Sec2.lipschitzWith_rightMarkDrift hr).continuous.measurable
    have h2 := (measurable_sampleFlow_pos hF).comp (hxj.prodMk (hx.prodMk ht))
    exact h2

end Positions

end LocalExt

end InteractingSLE
