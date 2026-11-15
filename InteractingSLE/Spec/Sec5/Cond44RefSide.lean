/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.MeanIdentArc
import InteractingSLE.WangWu.MeanIdentChamber
import InteractingSLE.WangWu.Prop418DetGlue
import InteractingSLE.Spec.Theorem15D5Borel
import InteractingSLE.Spec.Supplement.SBFrontier

/-!
# §4.2, Theorem 1.2 under (4.4): the flow line read from the counterflow range (deterministic part)

Packet PROVE-SEC5-N. Specification §4.2, proof of Theorem 1.2 for `κ ∈ (0, 4)` assuming (4.4)
(`source/spec/p097-144.md` L582–L586, p. 122): "Proposition 4.11 implies that the flow line `η` … is equal to the
left boundary of the counterflow line `η′` … Since `η` and `η′` are conditionally independent given `h`, it follows
that `η` is almost surely determined by `h`." The determination step needs the range of `η` as a *measurable*
function of the counterflow. This file proves the deterministic half: for a simple proper arc `γ` of `ℍ` from `0`
to `∞` (Wang–Wu's `IsProperArc`) and a set `K` (the completed counterflow range) with

* `arcRange γ ⊆ K` (Lemma 4.7: the counterflow contains the flow line), and
* `K ∩ leftSideOf (arcRange γ) = ∅` (Proposition 4.9: the counterflow lies to the right of the flow line),

the left side of `γ` is the set `LeftReach K` of points of `ℍ \ K` joined in `ℍ \ K` to a rational half-disc at a
negative real point that misses `K` (`mem_leftSideOf_iff_leftReach`), and the rational-disc hitting code of `γ` is
read from `K` alone (`hitCode_eq_lbCode`): a disc `B` meets `γ` iff `0 ∈ B`, or `B ∩ ℍ` meets the left side of `γ`
and contains a rational disc missing it. The measurability of these conditions in `K` is
`Cond44RefCode.lean`.
-/

set_option autoImplicit false

open Set Metric Filter Topology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Sec5.Cond44Ref

open WangWu hiding ratPt exists_ratPt_dist_lt
open Theorem15D5

variable {γ : ℝ → ℂ}

/-! ### The two sides of a proper arc -/

/-- Every point of a proper arc after its start is adherent to the right side of the arc (mirror of
`WangWu.IsProperArc.mem_closure_leftSideOf`). -/
theorem mem_closure_rightSideOf (hγ : IsProperArc γ) {s : ℝ} (hs : 0 < s) :
    γ s ∈ closure (rightSideOf (arcRange γ)) := by
  have hα := hγ.isDiscCrosscut_toDisc
  have hzH : γ s ∈ H := hγ.mem_H s hs
  have hzHb : γ s ∈ Hbar := le_of_lt (show (0 : ℝ) < (γ s).im from hzH)
  have hc : cayley (γ s) ∈ closure (crossSide (toDisc γ) (-1)) :=
    hα.crossRange_subset_closure_crossSide (Or.inr rfl)
      ((hγ.cayley_mem_crossRange_iff hzHb).2 ⟨s, mem_Ici.2 hs.le, rfl⟩)
  have hsub : cayleyInv '' crossSide (toDisc γ) (-1) ⊆ rightSideOf (arcRange γ) := by
    rintro _ ⟨w, hw, rfl⟩
    have hwb := (hα.crossSide_subset (Or.inr rfl) hw).1
    have hzw : cayleyInv w ∈ H := QuantumZipper.CA.cayleyInv_mem_H hwb
    rw [hγ.mem_rightSideOf_iff hzw, cayley_cayleyInv_of_mem_ball hwb]
    exact hw
  have hcont : ContinuousAt cayleyInv (cayley (γ s)) :=
    continuousAt_cayleyInv (cayley_ne_one_of_Hbar hzHb)
  have := mem_closure_image hcont hc
  rw [cayleyInv_cayley_of_mem_Hbar hzHb] at this
  exact closure_mono hsub this

theorem isOpen_leftSideOf_arcRange (hγ : IsProperArc γ) : IsOpen (leftSideOf (arcRange γ)) :=
  Theorem14.SB.isOpen_leftSideOf (by rw [hγ.isClosed_arcRange.closure_eq]; exact inter_subset_left)

theorem isOpen_rightSideOf_arcRange (hγ : IsProperArc γ) : IsOpen (rightSideOf (arcRange γ)) :=
  Theorem14.SB.isOpen_rightSideOf (by rw [hγ.isClosed_arcRange.closure_eq]; exact inter_subset_left)

theorem not_zero_mem_H : (0 : ℂ) ∉ H := fun h => by
  have h' : (0 : ℝ) < (0 : ℂ).im := h
  simp at h'

/-- A proper arc lies in `{0} ∪ ℍ`. -/
theorem mem_H_of_mem_arcRange (hγ : IsProperArc γ) {a : ℂ} (ha : a ∈ arcRange γ) (ha0 : a ≠ 0) : a ∈ H := by
  obtain ⟨t, ht, rfl⟩ := ha
  rcases (mem_Ici.1 ht).lt_or_eq with h | h
  · exact hγ.mem_H t h
  · exact absurd (by rw [← h, hγ.zero]) ha0

/-! ### Rational half-discs and the left reach set -/

/-- The rational half-disc `B(x, r) ∩ ℍ`. -/
def halfDisc (x r : ℚ) : Set ℂ := ball ((x : ℝ) : ℂ) (r : ℝ) ∩ H

theorem isOpen_halfDisc (x r : ℚ) : IsOpen (halfDisc x r) := isOpen_ball.inter QuantumZipper.isOpen_H

theorem isPreconnected_halfDisc (x r : ℚ) : IsPreconnected (halfDisc x r) :=
  ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected

/-- The centre of a rational half-disc is adherent to it. -/
theorem ofReal_mem_closure_halfDisc (x r : ℚ) (hr : 0 < r) : ((x : ℝ) : ℂ) ∈ closure (halfDisc x r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min ε (r : ℝ) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε := by have := min_le_left ε (r : ℝ); rw [hδ]; linarith
  have hδr : δ < r := by have := min_le_right ε (r : ℝ); rw [hδ]; linarith
  have hd : dist ((x : ℝ) : ℂ) (((x : ℝ) : ℂ) + (δ : ℂ) * Complex.I) = δ := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hδ0.le]
  refine ⟨((x : ℝ) : ℂ) + (δ : ℂ) * Complex.I, ⟨?_, ?_⟩, by rw [hd]; exact hδε⟩
  · rw [mem_ball, dist_comm, hd]
    exact hδr
  · show (0 : ℝ) < (((x : ℝ) : ℂ) + (δ : ℂ) * Complex.I).im
    simpa using hδ0

/-- A nonempty open set of `ℂ` contains a rational point. -/
theorem exists_ratPt_mem {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) : ∃ w : ℚ × ℚ, ratPt w ∈ U := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨w, hw⟩ := exists_ratPt_dist_lt z hε
  exact ⟨w, hb hw⟩

/-- **The left reach set of `K`**: `z ∈ ℍ \ K` lies in the component of `ℍ \ K` of a rational point of a rational
half-disc, centred at a negative real point, that misses `K`. -/
def LeftReach (K : Set ℂ) (z : ℂ) : Prop :=
  z ∈ H ∧ z ∉ K ∧ ∃ (x r : ℚ) (w : ℚ × ℚ), x < 0 ∧ 0 < r ∧ Disjoint (halfDisc x r) K ∧
    ratPt w ∈ halfDisc x r ∧ z ∈ connectedComponentIn (H \ K) (ratPt w)

/-- **The left side of the flow line is the left reach set of the counterflow range.** If `K` contains the proper
arc `γ` and misses its left side (`γ` is the left boundary of `K`), a point of `ℍ` lies on the left of `γ` iff it
reaches, in `ℍ \ K`, a rational half-disc at the negative axis missing `K`. -/
theorem mem_leftSideOf_iff_leftReach (hγ : IsProperArc γ) {K : Set ℂ} (hAK : arcRange γ ⊆ K)
    (hdis : Disjoint K (leftSideOf (arcRange γ))) {z : ℂ} :
    z ∈ leftSideOf (arcRange γ) ↔ LeftReach K z := by
  constructor
  · intro hz
    have hz' := hz
    obtain ⟨⟨hzH, hzA⟩, x, hx0, hxA, hxcl⟩ := hz
    set A := arcRange γ with hAdef
    set C := connectedComponentIn (H \ A) z with hCdef
    have hCL : C ⊆ leftSideOf A := fun w hw => mem_leftSideOf_of_mem_connectedComponentIn hz' hw
    have hCK : ∀ w ∈ C, w ∉ K := fun w hw hwK => disjoint_left.1 hdis hwK (hCL hw)
    -- a rational half-disc at `x` missing `A`
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 hγ.isClosed_arcRange.isOpen_compl _ hxA
    set m := min ε (-x) with hm
    have hm0 : 0 < m := lt_min hε (neg_pos.2 hx0)
    have hmε : m ≤ ε := min_le_left _ _
    have hmx : m ≤ -x := min_le_right _ _
    obtain ⟨x', hx'1, hx'2⟩ := exists_rat_btwn (show x - m / 3 < x + m / 3 by linarith)
    obtain ⟨r', hr'1, hr'2⟩ := exists_rat_btwn (show m / 3 < 2 * m / 3 by linarith)
    have hx'0 : (x' : ℝ) < 0 := by linarith
    have hr'0 : (0 : ℝ) < r' := by linarith
    have hdx : dist ((x' : ℝ) : ℂ) (x : ℂ) < m / 3 := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have hxB : (x : ℂ) ∈ ball ((x' : ℝ) : ℂ) (r' : ℝ) := by
      rw [mem_ball, dist_comm]
      linarith
    have hBsub : ball ((x' : ℝ) : ℂ) (r' : ℝ) ⊆ ball (x : ℂ) ε := by
      intro y hy
      rw [mem_ball] at hy ⊢
      calc dist y (x : ℂ) ≤ dist y ((x' : ℝ) : ℂ) + dist ((x' : ℝ) : ℂ) (x : ℂ) := dist_triangle _ _ _
        _ < r' + m / 3 := add_lt_add hy hdx
        _ ≤ ε := by linarith
    have hDA : halfDisc x' r' ⊆ H \ A := fun y hy => ⟨hy.2, hεA (hBsub hy.1)⟩
    -- the half-disc meets the component `C`, hence lies in it
    obtain ⟨c, hcB, hcC⟩ := (_root_.mem_closure_iff.1 hxcl) _ isOpen_ball hxB
    have hcD : c ∈ halfDisc x' r' := ⟨hcB, (connectedComponentIn_subset _ _ hcC).1⟩
    have hDC : halfDisc x' r' ⊆ C := by
      have := (isPreconnected_halfDisc x' r').subset_connectedComponentIn hcD hDA
      rwa [← connectedComponentIn_eq hcC] at this
    have hDK : Disjoint (halfDisc x' r') K := disjoint_left.2 fun y hy hyK => hCK y (hDC hy) hyK
    obtain ⟨w, hw⟩ := exists_ratPt_mem (isOpen_halfDisc x' r') hcD
    have hzK : z ∉ K := hCK z (mem_connectedComponentIn ⟨hzH, hzA⟩)
    have hCHK : C ⊆ H \ K := fun y hy => ⟨(connectedComponentIn_subset _ _ hy).1, hCK y hy⟩
    have hCsub : C ⊆ connectedComponentIn (H \ K) z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn ⟨hzH, hzA⟩) hCHK
    have hwz : ratPt w ∈ connectedComponentIn (H \ K) z := hCsub (hDC hw)
    refine ⟨hzH, hzK, x', r', w, by exact_mod_cast hx'0, by exact_mod_cast hr'0, hDK, hw, ?_⟩
    rw [← connectedComponentIn_eq hwz]
    exact mem_connectedComponentIn ⟨hzH, hzK⟩
  · rintro ⟨hzH, hzK, x, r, w, hx0, hr0, hDK, hwD, hzw⟩
    have hzA : z ∉ arcRange γ := fun h => hzK (hAK h)
    have hHK : H \ K ⊆ H \ arcRange γ := fun y hy => ⟨hy.1, fun h => hy.2 (hAK h)⟩
    have hx0' : (x : ℝ) < 0 := by exact_mod_cast hx0
    refine ⟨⟨hzH, hzA⟩, x, hx0', hγ.ofReal_notMem_arcRange hx0'.ne, ?_⟩
    have hDsub : halfDisc x r ⊆ connectedComponentIn (H \ K) (ratPt w) :=
      (isPreconnected_halfDisc x r).subset_connectedComponentIn hwD
        (fun y hy => ⟨hy.2, fun h => disjoint_left.1 hDK hy h⟩)
    have hcomp : connectedComponentIn (H \ K) (ratPt w) ⊆ connectedComponentIn (H \ arcRange γ) z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hzw
        ((connectedComponentIn_subset _ _).trans hHK)
    exact closure_mono (hDsub.trans hcomp) (ofReal_mem_closure_halfDisc x r hr0)

/-! ### Discs meeting a proper arc -/

/-- **An open preconnected `V ⊆ ℍ` meets a proper arc iff it meets the left side of the arc and a point outside the
closure of the left side** (the two sides partition `ℍ \ γ`, and every point of `γ` in `ℍ` is adherent to both). -/
theorem inter_arcRange_nonempty_iff (hγ : IsProperArc γ) {V : Set ℂ} (hV : IsOpen V) (hVc : IsPreconnected V)
    (hVH : V ⊆ H) :
    (V ∩ arcRange γ).Nonempty ↔
      (V ∩ leftSideOf (arcRange γ)).Nonempty ∧ (V \ closure (leftSideOf (arcRange γ))).Nonempty := by
  have hLo := isOpen_leftSideOf_arcRange hγ
  have hRo := isOpen_rightSideOf_arcRange hγ
  have hLR := hγ.disjoint_leftSideOf_rightSideOf
  constructor
  · rintro ⟨_, haV, t, ht, rfl⟩
    have ht0 : 0 < t := by
      rcases (mem_Ici.1 ht).lt_or_eq with h | h
      · exact h
      · have := hVH haV
        rw [← h, hγ.zero] at this
        exact absurd this not_zero_mem_H
    obtain ⟨p, hpV, hpL⟩ := _root_.mem_closure_iff.1 (hγ.mem_closure_leftSideOf ht0) V hV haV
    obtain ⟨q, hqV, hqR⟩ := _root_.mem_closure_iff.1 (mem_closure_rightSideOf hγ ht0) V hV haV
    exact ⟨⟨p, hpV, hpL⟩, q, hqV, disjoint_left.1 (hLR.symm.closure_right hRo) hqR⟩
  · rintro ⟨⟨p, hpV, hpL⟩, q, hqV, hqL⟩
    by_contra hne
    have hVLR : V ⊆ leftSideOf (arcRange γ) ∪ rightSideOf (arcRange γ) := fun y hy =>
      hγ.mem_leftSideOf_or_mem_rightSideOf (hVH hy) fun hyA => hne ⟨y, hy, hyA⟩
    have hVL : V ⊆ leftSideOf (arcRange γ) := hVc.subset_left_of_subset_union hLo hRo hLR hVLR ⟨p, hpV, hpL⟩
    exact hqL (subset_closure (hVL hqV))

/-- **The hitting condition read from `K`**: the rational disc `ratBall i` contains `0`, or it contains a rational
point of the left reach set of `K` and a rational disc inside `ℍ` none of whose rational points is in it. -/
def LBHit (K : Set ℂ) (i : ℚ × ℚ × ℚ) : Prop :=
  (0 : ℂ) ∈ ratBall i ∨ ((∃ p : ℚ × ℚ, ratPt p ∈ ratBall i ∧ LeftReach K (ratPt p)) ∧
    ∃ (p : ℚ × ℚ) (ρ : ℚ), 0 < ρ ∧ ball (ratPt p) (ρ : ℝ) ⊆ ratBall i ∩ H ∧
      ∀ q : ℚ × ℚ, ratPt q ∈ ball (ratPt p) (ρ : ℝ) → ¬ LeftReach K (ratPt q))

open Classical in
/-- **The hitting code read from `K`** (`1` on the discs satisfying `LBHit K`). -/
noncomputable def lbCode (K : Set ℂ) (i : ℚ × ℚ × ℚ) : ℝ := if LBHit K i then 1 else 0

/-- A proper arc meets an open set at a nonnegative rational time iff it meets it. -/
theorem exists_rat_mem_iff (hγ : IsProperArc γ) {U : Set ℂ} (hU : IsOpen U) :
    (∃ q : ℚ, 0 ≤ (q : ℝ) ∧ γ q ∈ U) ↔ (arcRange γ ∩ U).Nonempty := by
  classical
  constructor
  · rintro ⟨q, hq, hqU⟩
    exact ⟨γ q, ⟨q, mem_Ici.2 hq, rfl⟩, hqU⟩
  · intro hne
    obtain ⟨j, hjU, hj⟩ := (arcRange_inter_nonempty_iff_hitCode hγ.cont hU).1 hne
    unfold hitCode at hj
    split_ifs at hj with hex
    · obtain ⟨q, hq0, hq⟩ := hex
      exact ⟨q, hq0, hjU hq⟩
    · norm_num at hj

/-- **The rational-disc hitting events of `γ` read from `K`.** -/
theorem exists_rat_mem_ratBall_iff_lbHit (hγ : IsProperArc γ) {K : Set ℂ} (hAK : arcRange γ ⊆ K)
    (hdis : Disjoint K (leftSideOf (arcRange γ))) (i : ℚ × ℚ × ℚ) :
    (∃ q : ℚ, 0 ≤ (q : ℝ) ∧ γ q ∈ ratBall i) ↔ LBHit K i := by
  set L := leftSideOf (arcRange γ) with hLdef
  set V := ratBall i ∩ H with hVdef
  have hLo : IsOpen L := isOpen_leftSideOf_arcRange hγ
  have hVo : IsOpen V := isOpen_ball.inter QuantumZipper.isOpen_H
  have hVc : IsPreconnected V := ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hiff : ∀ y, y ∈ L ↔ LeftReach K y := fun y => mem_leftSideOf_iff_leftReach hγ hAK hdis
  rw [exists_rat_mem_iff hγ (U := ratBall i) isOpen_ball]
  -- step 1: split off the seed `0`
  have h1 : (arcRange γ ∩ ratBall i).Nonempty ↔ (0 : ℂ) ∈ ratBall i ∨ (V ∩ arcRange γ).Nonempty := by
    constructor
    · rintro ⟨a, haA, haB⟩
      by_cases ha0 : a = 0
      · exact Or.inl (ha0 ▸ haB)
      · exact Or.inr ⟨a, ⟨haB, mem_H_of_mem_arcRange hγ haA ha0⟩, haA⟩
    · rintro (h0 | ⟨a, haV, haA⟩)
      · exact ⟨0, ⟨0, mem_Ici.2 le_rfl, hγ.zero⟩, h0⟩
      · exact ⟨a, haA, haV.1⟩
  -- step 2: rational points of `V ∩ L`
  have h2 : (V ∩ L).Nonempty ↔ ∃ p : ℚ × ℚ, ratPt p ∈ ratBall i ∧ LeftReach K (ratPt p) := by
    constructor
    · rintro ⟨y, hyV, hyL⟩
      obtain ⟨p, hp⟩ := exists_ratPt_mem (hVo.inter hLo) ⟨hyV, hyL⟩
      exact ⟨p, hp.1.1, (hiff _).1 hp.2⟩
    · rintro ⟨p, hpB, hpL⟩
      exact ⟨ratPt p, ⟨hpB, hpL.1⟩, (hiff _).2 hpL⟩
  -- step 3: rational discs of `V` off the closure of `L`
  have h3 : (V \ closure L).Nonempty ↔ ∃ (p : ℚ × ℚ) (ρ : ℚ), 0 < ρ ∧ ball (ratPt p) (ρ : ℝ) ⊆ V ∧
      ∀ q : ℚ × ℚ, ratPt q ∈ ball (ratPt p) (ρ : ℝ) → ¬ LeftReach K (ratPt q) := by
    constructor
    · rintro ⟨y, hyV, hyL⟩
      obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 (hVo.sdiff isClosed_closure) y ⟨hyV, hyL⟩
      obtain ⟨p, hp⟩ := exists_ratPt_dist_lt y (show 0 < ε / 3 by positivity)
      obtain ⟨ρ, hρ1, hρ2⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 3 by positivity)
      have hsub : ball (ratPt p) (ρ : ℝ) ⊆ V \ closure L := by
        intro u hu
        apply hεs
        rw [mem_ball] at hu ⊢
        calc dist u y ≤ dist u (ratPt p) + dist (ratPt p) y := dist_triangle _ _ _
          _ < ρ + ε / 3 := add_lt_add hu hp
          _ < ε := by linarith
      refine ⟨p, ρ, by exact_mod_cast hρ1, fun u hu => (hsub hu).1, fun q hq hqL => ?_⟩
      exact (hsub hq).2 (subset_closure ((hiff _).2 hqL))
    · rintro ⟨p, ρ, hρ, hsub, hq⟩
      have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
      refine ⟨ratPt p, hsub (mem_ball_self hρ'), fun hpL => ?_⟩
      obtain ⟨u, huB, huL⟩ := _root_.mem_closure_iff.1 hpL _ isOpen_ball (mem_ball_self hρ')
      obtain ⟨q, hqB, hqL⟩ := exists_ratPt_mem (isOpen_ball.inter hLo) ⟨huB, huL⟩
      exact hq q hqB ((hiff _).1 hqL)
  rw [h1, inter_arcRange_nonempty_iff hγ hVo hVc inter_subset_right, h2, h3]
  rfl

/-- **The hitting code of the flow line is read from the counterflow set**: if `K` contains the proper arc `γ`
and misses its left side, then `hitCode γ = lbCode K`. -/
theorem hitCode_eq_lbCode (hγ : IsProperArc γ) {K : Set ℂ} (hAK : arcRange γ ⊆ K)
    (hdis : Disjoint K (leftSideOf (arcRange γ))) : hitCode γ = lbCode K := by
  funext i
  have e := exists_rat_mem_ratBall_iff_lbHit hγ hAK hdis i
  unfold hitCode lbCode
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (e.1 h1) h2
  · exact absurd (e.2 h2) h1
  · rfl

/-! ### The two inputs from rational times -/

/-- **Containment from rational times**: a proper arc whose points at positive rational times lie in `closure S`
lies in `closure S`. -/
theorem arcRange_subset_closure_of_forall_rat (hγ : IsProperArc γ) {S : Set ℂ}
    (hpos : ∀ t : ℚ, 0 < t → γ t ∈ closure S) : arcRange γ ⊆ closure S := by
  rintro _ ⟨t, ht, rfl⟩
  choose q hq using fun n : ℕ => exists_rat_btwn (show t < t + 1 / ((n : ℝ) + 1) by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith)
  have hqt : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 t) := by
    have hup : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (hq n).1.le)
      fun n => (hq n).2.le
  have hqt' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[Ici 0] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hqt, Eventually.of_forall fun n => mem_Ici.2 ((mem_Ici.1 ht).trans (hq n).1.le)⟩
  have hlim : Tendsto (fun n => γ (q n)) atTop (𝓝 (γ t)) := (hγ.cont t ht).tendsto.comp hqt'
  have hpos' : ∀ n, 0 < q n := fun n => by
    have : (0 : ℝ) < q n := lt_of_le_of_lt (mem_Ici.1 ht) (hq n).1
    exact_mod_cast this
  have := mem_closure_of_tendsto hlim (Eventually.of_forall fun n => hpos (q n) (hpos' n))
  rwa [closure_closure] at this

/-- **Avoidance from a dense family**: if no point of `S` is on the left of `γ`, neither is any point of
`closure S`. -/
theorem disjoint_closure_leftSideOf (hγ : IsProperArc γ) {S : Set ℂ}
    (hS : ∀ y ∈ S, y ∉ leftSideOf (arcRange γ)) : Disjoint (closure S) (leftSideOf (arcRange γ)) :=
  (disjoint_left.2 fun y hy => hS y hy).closure_left (isOpen_leftSideOf_arcRange hγ)

end InteractingSLE.Sec5.Cond44Ref
