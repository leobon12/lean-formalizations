/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Data.NNRat.Encodable

/-!
# Lemma 7.1's pocket: the capacity-time stopping rule (Galmarino for every coordinate function)

Packet PROVE-LEMMA71I, part (β). The three-curve law `Sec6.Three.ae_condExp_exp_eq_three_of_tendsto` (and its
conditioned form `Lemma71G.ae_condExp_exp_eq_three_of_le`) takes the stopping time `τ` of the middle curve as a **path
functional** (ruling R37): `τ ω = S (hist β) (hist α) (pathCoord γ)` with `S` jointly measurable and with the inclusive
Galmarino property for **all** coordinate functions `c : ℚ≥0 → ℂ`, not only for continuous paths. In Lemma 7.1 the time
is the original time `τ_t` at which the mapped segment reaches half-plane capacity `2t` (specification p. 224: "For
each bounded stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies"). The capacity of
the mapped prefix is read through countably many coordinates, and the naive inverse of the capacity clock (`capInv`,
`Classical.choose`) is not Galmarino off continuous paths (PROVE-LEMMA71H, obstruction G6).

**Construction.** Let `f q x c` (`q ∈ ℚ≥0`) be any family of `[0, ∞]`-valued functionals that are measurable and
depend on `c` only through its coordinates at rationals `≤ q` (for Lemma 7.1: the grid capacity
`WholeField.hcapHit` of the chart image of the coordinates `c r`, `r ≤ q`, lying in the closed pocket). Put

* `runSup f x c u = ⨆_{q ≤ u} f q x c` (the running supremum, for real `u ∈ [0, ∞]`);
* `levelInf f a x c = inf {q ∈ ℚ≥0 : a ≤ runSup f x c q}`;
* `levelRule f a x c = levelInf f a x c` if `a ≤ runSup f x c (levelInf f a x c)`, and `⊤` otherwise.

Then (`measurable_levelRule`) `levelRule` is measurable, and (`levelRule_galmarino`) it is Galmarino for every `c`:
if `c'` agrees with `c` at all rationals `≤ levelRule f a x c`, then `levelRule f a x c' = levelRule f a x c`. No
continuity is needed: the running supremum at a real time is a countable supremum of coordinates up to that time, so
it is local, and its value at the random time `levelInf` is a countable supremum of measurable functions.
(`levelRule_eq_of_continuous`) For a continuous monotone clock `g` with `f q x c = g q` at rationals (the capacity of
the mapped prefix along an actual continuous path), `levelRule` is the first time `g` reaches `a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71I

section Rule

variable {X E : Type*}

/-- The running supremum `⨆_{q ≤ u} f q x c` of a rational family of functionals. -/
def runSup (f : ℚ≥0 → X → (ℚ≥0 → E) → ℝ≥0∞) (x : X) (c : ℚ≥0 → E) (u : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ q : ℚ≥0, if ((q : ℝ≥0) : ℝ≥0∞) ≤ u then f q x c else 0

/-- The first rational time at which the running supremum reaches the level `a`. -/
def levelInf (f : ℚ≥0 → X → (ℚ≥0 → E) → ℝ≥0∞) (a : ℝ≥0∞) (x : X) (c : ℚ≥0 → E) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if a ≤ runSup f x c ((q : ℝ≥0) : ℝ≥0∞) then ((q : ℝ≥0) : ℝ≥0∞) else ⊤

open scoped Classical in
/-- **The level stopping rule**: `levelInf` if the level is reached there, `⊤` otherwise. -/
def levelRule (f : ℚ≥0 → X → (ℚ≥0 → E) → ℝ≥0∞) (a : ℝ≥0∞) (x : X) (c : ℚ≥0 → E) : ℝ≥0∞ :=
  if a ≤ runSup f x c (levelInf f a x c) then levelInf f a x c else ⊤

variable {f : ℚ≥0 → X → (ℚ≥0 → E) → ℝ≥0∞} {a : ℝ≥0∞}

theorem le_runSup {x : X} {c : ℚ≥0 → E} {u : ℝ≥0∞} {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) ≤ u) :
    f q x c ≤ runSup f x c u := by
  refine le_trans ?_ (le_iSup _ q)
  simp only [hq, ↓reduceIte, le_refl]

theorem runSup_mono {x : X} {c : ℚ≥0 → E} : Monotone (runSup f x c) := fun u v huv =>
  iSup_mono fun q => by
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans huv) h2
    · exact zero_le
    · exact le_rfl

/-- The running supremum at `u` depends only on the coordinates at rationals `≤ u`. -/
theorem runSup_congr (hloc : ∀ q x c c', (∀ r : ℚ≥0, r ≤ q → c r = c' r) → f q x c' = f q x c) {x : X}
    {c c' : ℚ≥0 → E} {u : ℝ≥0∞} (h : ∀ r : ℚ≥0, ((r : ℝ≥0) : ℝ≥0∞) ≤ u → c r = c' r) :
    runSup f x c' u = runSup f x c u :=
  iSup_congr fun q => by
    split_ifs with hq
    · refine hloc q x c c' fun r hr => h r (le_trans ?_ hq)
      exact_mod_cast hr
    · rfl

/-- **Density**: the infimum of the rationals `≥ T` is `T` (for `T < ∞`). -/
theorem iInf_ite_le_eq {T : ℝ≥0∞} (hT : T ≠ ⊤) :
    (⨅ q : ℚ≥0, if T ≤ ((q : ℝ≥0) : ℝ≥0∞) then ((q : ℝ≥0) : ℝ≥0∞) else ⊤) = T := by
  refine le_antisymm (le_of_forall_gt fun b hb => ?_) (le_iInf fun q => ?_)
  · lift T to ℝ≥0 using hT
    obtain ⟨r, hTr, hrb⟩ : ∃ r : ℝ, (T : ℝ) < r ∧ ENNReal.ofReal r < b := by
      rcases eq_or_ne b ⊤ with rfl | hb'
      · exact ⟨T + 1, by linarith, ENNReal.ofReal_lt_top⟩
      · lift b to ℝ≥0 using hb'
        refine ⟨((T : ℝ) + b) / 2, ?_, ?_⟩
        · have : (T : ℝ) < b := by exact_mod_cast hb
          linarith
        · rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ENNReal.coe_ne_top]
          have : (T : ℝ) < b := by exact_mod_cast hb
          simp only [ENNReal.coe_toReal]
          linarith
    obtain ⟨q, hTq, hqr⟩ := exists_rat_btwn hTr
    have hq0 : (0 : ℚ) ≤ q := by
      have : (0 : ℝ) < q := lt_of_le_of_lt T.2 hTq
      exact_mod_cast this.le
    set q' : ℚ≥0 := q.toNNRat with hq'
    have hq'r : ((q' : ℝ≥0) : ℝ) = q := by
      have : ((q' : ℝ≥0) : ℝ) = ((q' : ℚ) : ℝ) := rfl
      rw [this, hq', Rat.coe_toNNRat q hq0]
    have hTq' : (T : ℝ≥0∞) ≤ ((q' : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, hq'r]
      exact hTq.le
    refine lt_of_le_of_lt (iInf_le _ q') ?_
    simp only [hTq', ↓reduceIte]
    refine lt_of_le_of_lt ?_ hrb
    rw [← ENNReal.ofReal_coe_nnreal, hq'r]
    exact ENNReal.ofReal_le_ofReal hqr.le
  · split_ifs with h
    · exact h
    · exact le_top

/-- **The level stopping rule is Galmarino for every coordinate function**: if `c'` agrees with `c` at all rationals
`≤ levelRule f a x c`, then `levelRule f a x c' = levelRule f a x c`. -/
theorem levelRule_galmarino (hloc : ∀ q x c c', (∀ r : ℚ≥0, r ≤ q → c r = c' r) → f q x c' = f q x c)
    (x : X) (c c' : ℚ≥0 → E)
    (h : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ levelRule f a x c → c q = c' q) :
    levelRule f a x c' = levelRule f a x c := by
  classical
  set T := levelInf f a x c with hTdef
  by_cases hreach : a ≤ runSup f x c T
  swap
  · have hrule : levelRule f a x c = ⊤ := by
      simp only [levelRule, ← hTdef, hreach, ↓reduceIte]
    have hcc : c' = c := funext fun q => (h q (by rw [hrule]; exact le_top)).symm
    rw [hcc]
  have hrule : levelRule f a x c = T := by
    simp only [levelRule, ← hTdef, hreach, ↓reduceIte]
  rw [hrule] at h ⊢
  by_cases hTtop : T = ⊤
  · have hcc : c' = c := funext fun q => (h q (by rw [hTtop]; exact le_top)).symm
    rw [hcc]
    exact hrule
  -- the running suprema agree up to `T`
  have hagree : ∀ u ≤ T, runSup f x c' u = runSup f x c u := fun u hu =>
    runSup_congr hloc fun r hr => h r (hr.trans hu)
  have hT' : levelInf f a x c' = T := by
    refine le_antisymm ?_ (le_iInf fun q => ?_)
    · unfold levelInf
      calc (⨅ q : ℚ≥0, if a ≤ runSup f x c' ((q : ℝ≥0) : ℝ≥0∞) then ((q : ℝ≥0) : ℝ≥0∞) else ⊤)
          ≤ ⨅ q : ℚ≥0, if T ≤ ((q : ℝ≥0) : ℝ≥0∞) then ((q : ℝ≥0) : ℝ≥0∞) else ⊤ := iInf_mono fun q => ?_
        _ = T := iInf_ite_le_eq hTtop
      by_cases h2 : T ≤ ((q : ℝ≥0) : ℝ≥0∞)
      · have h1 : a ≤ runSup f x c' ((q : ℝ≥0) : ℝ≥0∞) :=
          le_trans (by rw [hagree T le_rfl]; exact hreach) (runSup_mono h2)
        simp only [h1, h2, ↓reduceIte, le_refl]
      · simp only [h2, ↓reduceIte, le_top]
    · split_ifs with hq
      · by_contra hlt
        have hlt' : ((q : ℝ≥0) : ℝ≥0∞) < T := not_le.1 hlt
        rw [hagree _ hlt'.le] at hq
        have : T ≤ ((q : ℝ≥0) : ℝ≥0∞) := by
          refine iInf_le_of_le q ?_
          simp only [hq, ↓reduceIte, le_refl]
        exact absurd this (not_le.2 hlt')
      · exact le_top
  have hreach' : a ≤ runSup f x c' (levelInf f a x c') := by
    rw [hT', hagree T le_rfl]
    exact hreach
  have h3 : a ≤ runSup f x c' T := hT' ▸ hreach'
  simp only [levelRule, hT', h3, ↓reduceIte]

/-- **The level stopping rule is measurable.** -/
theorem measurable_levelRule [MeasurableSpace X] [MeasurableSpace E]
    (hm : ∀ q, Measurable fun z : X × (ℚ≥0 → E) => f q z.1 z.2) :
    Measurable fun z : X × (ℚ≥0 → E) => levelRule f a z.1 z.2 := by
  classical
  have hrun : ∀ u : ℝ≥0∞, Measurable fun z : X × (ℚ≥0 → E) => runSup f z.1 z.2 u := fun u =>
    Measurable.iSup fun q => by
      by_cases hq : ((q : ℝ≥0) : ℝ≥0∞) ≤ u
      · simp only [hq, ↓reduceIte]; exact hm q
      · simp only [hq, ↓reduceIte]; exact measurable_const
  have hinf : Measurable fun z : X × (ℚ≥0 → E) => levelInf f a z.1 z.2 :=
    Measurable.iInf fun q =>
      Measurable.ite (measurableSet_le measurable_const (hrun _)) measurable_const measurable_const
  have hrunT : Measurable fun z : X × (ℚ≥0 → E) => runSup f z.1 z.2 (levelInf f a z.1 z.2) :=
    Measurable.iSup fun q =>
      Measurable.ite (measurableSet_le measurable_const hinf) (hm q) measurable_const
  exact Measurable.ite (measurableSet_le measurable_const hrunT) hinf measurable_const

/-! ### Identification along a continuous clock -/

/-- Rationals approximate every `u ∈ ℝ≥0` from below. -/
theorem exists_nnrat_le_dist_lt (u : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ≥0, (q : ℝ≥0) ≤ u ∧ dist (q : ℝ≥0) u < δ := by
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, by simp, by simpa using hδ⟩
  have hu0 : (0 : ℝ) < u := by exact_mod_cast pos_iff_ne_zero.2 hu
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max ((u : ℝ) - δ) 0 < u from max_lt (by linarith) hu0)
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have hqd : (u : ℝ) - δ < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hq0' : (0 : ℚ) ≤ q := by exact_mod_cast hq0.le
  have hq'r : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = q := by
    have : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) := rfl
    rw [this, Rat.coe_toNNRat q hq0']
  refine ⟨q.toNNRat, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, hq'r]
    exact hq2.le
  · rw [NNReal.dist_eq, hq'r, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-- **Along a continuous monotone clock the running supremum is the clock**: if `f q x c = g q` at rationals, then
`runSup f x c u = g u` for every finite `u`. -/
theorem runSup_eq_of_continuous {g : ℝ≥0 → ℝ≥0∞} (hg : Continuous g) (hgm : Monotone g) {x : X}
    {c : ℚ≥0 → E} (hf : ∀ q : ℚ≥0, f q x c = g q) (u : ℝ≥0) : runSup f x c u = g u := by
  refine le_antisymm (iSup_le fun q => ?_) (le_of_forall_lt fun b hb => ?_)
  · by_cases hq : ((q : ℝ≥0) : ℝ≥0∞) ≤ u
    · simp only [hq, ↓reduceIte, hf]
      exact hgm (by exact_mod_cast hq)
    · simp only [hq, ↓reduceIte]
      exact zero_le
  · have hU : IsOpen (g ⁻¹' Ioi b) := isOpen_Ioi.preimage hg
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU u hb
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_le_dist_lt u hδ
    have hbq : b < g q := hball (Metric.mem_ball.2 hq2)
    refine lt_of_lt_of_le hbq ?_
    rw [← hf]
    exact le_runSup (by exact_mod_cast hq1)

/-- **Along a continuous monotone clock the level rule is the first hitting time of the level**: if `f q x c = g q`
at rationals, `a ≤ g T` and `g u < a` for `u < T`, then `levelRule f a x c = T`. -/
theorem levelRule_eq_of_continuous {g : ℝ≥0 → ℝ≥0∞} (hg : Continuous g) (hgm : Monotone g) {x : X}
    {c : ℚ≥0 → E} (hf : ∀ q : ℚ≥0, f q x c = g q) {T : ℝ≥0} (hT : a ≤ g T) (hlt : ∀ u < T, g u < a) :
    levelRule f a x c = T := by
  classical
  have hiff : ∀ q : ℚ≥0, a ≤ runSup f x c ((q : ℝ≥0) : ℝ≥0∞) ↔ (T : ℝ≥0∞) ≤ ((q : ℝ≥0) : ℝ≥0∞) := by
    intro q
    rw [runSup_eq_of_continuous hg hgm hf, ENNReal.coe_le_coe]
    constructor
    · intro h
      by_contra hlt'
      exact absurd h (not_le.2 (hlt _ (not_le.1 hlt')))
    · intro h
      exact hT.trans (hgm h)
  have hinf : levelInf f a x c = T := by
    unfold levelInf
    simp_rw [hiff]
    exact iInf_ite_le_eq ENNReal.coe_ne_top
  have hreach : a ≤ runSup f x c (T : ℝ≥0∞) := by
    rw [runSup_eq_of_continuous hg hgm hf]
    exact hT
  simp only [levelRule, hinf, hreach, ↓reduceIte]

end Rule

end InteractingSLE.Sec7.Lemma71I
