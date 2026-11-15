/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw2Real

/-!
# Records and threshold events of a launch, by countable operations (deterministic)

Packet PROVE-STAGEDLAW2. `ExplState.launch` updates the right record by
`recR' = sSup (insert recR {x | recR < x ∧ ¬ alive x})` and decides a right threshold by `∃ x, recR < x ∧ hit x`,
quantifying over uncountably many real points `x`, read in the current chart `x ↦ m x`. On a chart profile
`RightGood m a` (`m` continuous, strictly increasing and unbounded above on `(a, ∞)`) and for alive sets with the
shape of `IsRealHalf`, both are expressed through countably many points and two explicit candidates:

* `exists_lt_iff_rat`: `∃ x > a, m x < y` iff some rational `q > a` has `m q < y`;
* `exists_eq_iff_exists_lt`: on `(a, ∞)`, `m` takes exactly the values `y` above some value (intermediate values);
* `sSup_insert_le_iff`: for a good driver, `recR' ≤ c` iff `a ≤ c` and `c⁺ ≤ m q` for every rational
  `q > max a c`, where `c⁺ = inf {y > 0 alive}`;
* `rightGood_comp`: after the launch, the new profile `f ∘ m` is good on `(recR', ∞)`;
* **`exists_hit_iff`**: `∃ x > a, hit (m x)` iff some rational, or one of the two candidates
  `c⁺ = inf {y > 0 | alive at T}`, `c⁻ = sup {y < 0 | alive at T}`, is a hit value above some value of `m`
  (a hit set without rationals is a single point, and that point is a candidate).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Exist

namespace StagedLaw

/-- **A good right profile**: `m` is continuous, strictly increasing and unbounded above on `(a, ∞)`. -/
def RightGood (m : ℝ → ℝ) (a : ℝ) : Prop :=
  StrictMonoOn m (Ioi a) ∧ ContinuousOn m (Ioi a) ∧ ∀ M, ∃ x, a < x ∧ M < m x

section Profile

variable {m : ℝ → ℝ} {a : ℝ}

theorem RightGood.mono_of_le (h : RightGood m a) {a' : ℝ} (haa' : a ≤ a') : RightGood m a' := by
  refine ⟨h.1.mono (Ioi_subset_Ioi haa'), h.2.1.mono (Ioi_subset_Ioi haa'), fun M => ?_⟩
  obtain ⟨x, hx, hMx⟩ := h.2.2 (max M (m (a' + 1)))
  refine ⟨x, ?_, (le_max_left _ _).trans_lt hMx⟩
  by_contra hle
  push Not at hle
  have h1 : m x < m (a' + 1) := h.1 hx (show a < a' + 1 by linarith) (by linarith)
  linarith [le_max_right M (m (a' + 1))]

theorem RightGood.sub_const (h : RightGood m a) (c : ℝ) : RightGood (fun x => m x - c) a := by
  refine ⟨fun x hx y hy hxy => by simpa using h.1 hx hy hxy, h.2.1.sub continuousOn_const, fun M => ?_⟩
  obtain ⟨x, hx, hMx⟩ := h.2.2 (M + c)
  exact ⟨x, hx, by linarith⟩

theorem RightGood.congr (h : RightGood m a) {m' : ℝ → ℝ} (he : EqOn m m' (Ioi a)) : RightGood m' a := by
  refine ⟨fun x hx y hy hxy => by rw [← he hx, ← he hy]; exact h.1 hx hy hxy, h.2.1.congr fun x hx => (he hx).symm,
    fun M => ?_⟩
  obtain ⟨x, hx, hMx⟩ := h.2.2 M
  exact ⟨x, hx, by rw [← he hx]; exact hMx⟩

/-- Values of `m` below `y` are witnessed at rational points. -/
theorem exists_lt_iff_rat (h : RightGood m a) {y : ℝ} :
    (∃ x, a < x ∧ m x < y) ↔ ∃ q : ℚ, a < q ∧ m q < y := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
    exact ⟨q, hq1, (h.1 hq1 hx hq2).trans hxy⟩
  · rintro ⟨q, hq, hqy⟩
    exact ⟨q, hq, hqy⟩

/-- **Intermediate values**: on `(a, ∞)`, `m` takes the value `y` iff it takes a value below `y`. -/
theorem exists_eq_iff_exists_lt (h : RightGood m a) {y : ℝ} :
    (∃ x, a < x ∧ m x = y) ↔ ∃ x, a < x ∧ m x < y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', hx'1, hx'2⟩ := exists_between hx
    exact ⟨x', hx'1, h.1 hx'1 (hx'1.trans hx'2) hx'2⟩
  · rintro ⟨x₁, hx₁, hlt⟩
    obtain ⟨x₂, hx₂, hgt⟩ := h.2.2 y
    have h12 : x₁ ≤ x₂ := by
      by_contra hle
      push Not at hle
      exact absurd (h.1 hx₂ hx₁ hle) (by linarith)
    have hsub : Icc x₁ x₂ ⊆ Ioi a := fun z hz => hx₁.trans_le hz.1
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc h12 (h.2.1.mono hsub) ⟨hlt.le, hgt.le⟩
    exact ⟨x, hsub hx, hxy⟩

/-- A lower bound on `(b, ∞)` is checked at rational points. -/
theorem forall_le_iff_rat (h : RightGood m a) {b c : ℝ} (hab : a ≤ b) :
    (∀ x, b < x → c ≤ m x) ↔ ∀ q : ℚ, b < q → c ≤ m q := by
  refine ⟨fun H q hq => H q hq, fun H x hx => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hx
  exact (H q hq1).trans (h.1 (hab.trans_lt hq1) (hab.trans_lt hx) hq2).le

end Profile

/-! ### The right record after a launch -/

section Record

variable {m : ℝ → ℝ} {a : ℝ} {A : ℝ → Prop} {f : ℝ → ℝ}

/-- The infimum of the positive alive points. -/
def posInf (A : ℝ → Prop) : ℝ := sInf {y | 0 < y ∧ A y}

/-- The supremum of the negative alive points. -/
def negSup (A : ℝ → Prop) : ℝ := sSup {y | y < 0 ∧ A y}

theorem posInf_nonneg (A : ℝ → Prop) : 0 ≤ posInf A := Real.sInf_nonneg fun _ hy => hy.1.le

theorem negSup_nonpos (A : ℝ → Prop) : negSup A ≤ 0 := Real.sSup_nonpos fun _ hy => hy.1.le

theorem posInf_le {y : ℝ} (hy : 0 < y) (hAy : A y) : posInf A ≤ y :=
  csInf_le ⟨0, fun _ hz => hz.1.le⟩ ⟨hy, hAy⟩

/-- Above `c⁺` everything is alive. -/
theorem alive_of_posInf_lt (hA : IsRealHalf A f) {y : ℝ} (hy : posInf A < y) : A y := by
  obtain ⟨M, hM⟩ := hA.2.2.1
  have hne : {y | 0 < y ∧ A y}.Nonempty := ⟨max M 1, by positivity, hM _ (le_max_left _ _)⟩
  obtain ⟨z, ⟨hz0, hzA⟩, hzy⟩ := exists_lt_of_csInf_lt hne hy
  exact hA.2.1 z y hz0 hzy hzA

theorem not_alive_of_lt_posInf {y : ℝ} (hy : 0 < y) (hy' : y < posInf A) : ¬ A y := fun hAy =>
  absurd (csInf_le ⟨0, fun _ hz => hz.1.le⟩ ⟨hy, hAy⟩ : posInf A ≤ y) (not_le.2 hy')

/-- The new right record of a launch. -/
def newRec (m : ℝ → ℝ) (a : ℝ) (A : ℝ → Prop) : ℝ := sSup (insert a {x | a < x ∧ ¬ A (m x)})

theorem bddAbove_dead (hm : RightGood m a) (hA : IsRealHalf A f) :
    BddAbove (insert a {x | a < x ∧ ¬ A (m x)}) := by
  obtain ⟨x₀, hx₀, hm₀⟩ := hm.2.2 (posInf A)
  refine ⟨max a x₀, fun x hx => ?_⟩
  rcases hx with rfl | ⟨hxa, hxA⟩
  · exact le_max_left _ _
  · by_contra hlt
    push Not at hlt
    have : m x₀ < m x := hm.1 hx₀ hxa ((le_max_right _ _).trans_lt hlt)
    exact hxA (alive_of_posInf_lt hA (hm₀.trans this))

theorem le_newRec (hm : RightGood m a) (hA : IsRealHalf A f) : a ≤ newRec m a A :=
  le_csSup (bddAbove_dead hm hA) (mem_insert _ _)

/-- Above the new record, the chart values are positive and alive. -/
theorem pos_alive_of_newRec_lt (hm : RightGood m a) (hA : IsRealHalf A f) {x : ℝ} (hx : newRec m a A < x) :
    0 < m x ∧ A (m x) := by
  have hxa : a < x := (le_newRec hm hA).trans_lt hx
  have hbdd := bddAbove_dead hm hA
  have hnot : ∀ z, newRec m a A < z → A (m z) := fun z hz => by
    by_contra hA'
    have : z ≤ newRec m a A := le_csSup hbdd (Or.inr ⟨(le_newRec hm hA).trans_lt hz, hA'⟩)
    linarith
  refine ⟨?_, hnot x hx⟩
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · -- a zero of `m` after the record
    obtain ⟨z, hz, hmz⟩ := (exists_eq_iff_exists_lt (hm.mono_of_le (le_newRec hm hA)) (y := 0)).2 ⟨x, hx, hlt⟩
    exact hA.1 (hmz ▸ hnot z hz)
  · exact hA.1 (heq ▸ hnot x hx)

theorem posInf_lt_of_newRec_lt (hm : RightGood m a) (hA : IsRealHalf A f) {x : ℝ} (hx : newRec m a A < x) :
    posInf A < m x := by
  by_contra hle
  push Not at hle
  obtain ⟨x', hx'1, hx'2⟩ := exists_between hx
  have hx'a : a < x' := (le_newRec hm hA).trans_lt hx'1
  obtain ⟨hpos, hAx'⟩ := pos_alive_of_newRec_lt hm hA hx'1
  have hlt : m x' < m x := hm.1 hx'a (hx'a.trans hx'2) hx'2
  exact not_alive_of_lt_posInf hpos (hlt.trans_le hle) hAx'

/-- **The new record by countably many conditions.** -/
theorem newRec_le_iff (hm : RightGood m a) (hA : IsRealHalf A f) (c : ℝ) :
    newRec m a A ≤ c ↔ a ≤ c ∧ ∀ q : ℚ, max a c < q → posInf A ≤ m q := by
  constructor
  · intro h
    exact ⟨(le_newRec hm hA).trans h, fun q hq =>
      (posInf_lt_of_newRec_lt hm hA (h.trans_lt ((le_max_right _ _).trans_lt hq))).le⟩
  · rintro ⟨hac, H⟩
    have H' := (forall_le_iff_rat hm (le_max_left a c)).2 H
    refine csSup_le (insert_nonempty _ _) fun z hz => ?_
    rcases hz with rfl | ⟨hza, hzA⟩
    · exact hac
    · by_contra hzc
      push Not at hzc
      obtain ⟨x, hx1, hx2⟩ := exists_between (max_lt hza hzc)
      have hlt : m x < m z := hm.1 ((le_max_left _ _).trans_lt hx1) hza hx2
      exact hzA (alive_of_posInf_lt hA ((H' x hx1).trans_lt hlt))

/-- **After the launch the profile is good again**: `f ∘ m` on `(recR', ∞)`. -/
theorem rightGood_comp (hm : RightGood m a) (hA : IsRealHalf A f) : RightGood (fun x => f (m x)) (newRec m a A) := by
  have hle := le_newRec hm hA
  refine ⟨fun x hx y hy hxy => ?_, ?_, fun M => ?_⟩
  · obtain ⟨hx0, hxA⟩ := pos_alive_of_newRec_lt hm hA hx
    obtain ⟨-, hyA⟩ := pos_alive_of_newRec_lt hm hA hy
    exact hA.2.2.2.2.1 _ _ hx0 (hm.1 (hle.trans_lt hx) (hle.trans_lt hy) hxy) hxA hyA
  · intro x hx
    obtain ⟨hx0, hxA⟩ := pos_alive_of_newRec_lt hm hA hx
    have hmc : ContinuousWithinAt m (Ioi (newRec m a A)) x :=
      (hm.2.1.mono (Ioi_subset_Ioi hle)) x hx
    rw [Metric.continuousWithinAt_iff] at hmc ⊢
    intro ε hε
    obtain ⟨η, hη, hfη⟩ := hA.2.2.2.2.2.1 (m x) hx0 hxA ε hε
    obtain ⟨δ, hδ, hmδ⟩ := hmc η hη
    refine ⟨δ, hδ, fun y hy hyx => ?_⟩
    have h1 := hmδ hy hyx
    rw [Real.dist_eq] at h1 ⊢
    exact hfη (m y) (pos_alive_of_newRec_lt hm hA hy).2 h1
  · obtain ⟨N, hN⟩ := hA.2.2.2.2.2.2 (M + 1)
    obtain ⟨x, hx, hNx⟩ := (hm.mono_of_le hle).2.2 N
    exact ⟨x, hx, by linarith [hN (m x) hNx.le (pos_alive_of_newRec_lt hm hA hx).2]⟩

/-- When nothing is alive, the new record is the junk value `0`. -/
theorem newRec_of_dead (hm : RightGood m a) (hA : ∀ y, ¬ A y) : newRec m a A = 0 := by
  refine Real.sSup_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  obtain ⟨x, hx, hBx⟩ := hm.2.2 0
  obtain ⟨x', hx'⟩ := exists_gt (max B x)
  have : x' ≤ B := hB (Or.inr ⟨hx.trans ((le_max_right _ _).trans_lt hx'), hA _⟩)
  linarith [le_max_left B x]

/-- On a constant profile the new record is `a` or the junk value `0`. -/
theorem newRec_of_const {c : ℝ} (hc : ∀ x, m x = c) [Decidable (A c)] :
    newRec m a A = if A c then a else 0 := by
  unfold newRec
  split_ifs with h
  · have : {x | a < x ∧ ¬ A (m x)} = ∅ := by
      ext x; simp [hc, h]
    rw [this, insert_empty_eq, csSup_singleton]
  · refine Real.sSup_of_not_bddAbove fun ⟨B, hB⟩ => ?_
    obtain ⟨x', hx'⟩ := exists_gt (max B a)
    have : x' ≤ B := hB (Or.inr ⟨(le_max_right _ _).trans_lt hx', by rw [hc]; exact h⟩)
    linarith [le_max_left B a]

end Record


/-! ### The threshold events -/

section Hit

variable {m : ℝ → ℝ} {a : ℝ}

/-- The order shape of an alive set on the real line: up-set on `(0, ∞)`, down-set on `(−∞, 0)`. -/
def IsUpDown (A : ℝ → Prop) : Prop :=
  (∀ q y, 0 < q → q < y → A q → A y) ∧ (∀ q y, y < q → q < 0 → A q → A y)

theorem IsRealFlow.isUpDown {A : ℝ → Prop} {f : ℝ → ℝ} (h : IsRealFlow A f) : IsUpDown A := by
  refine ⟨h.1.2.1, fun q y hyq hq0 hA => ?_⟩
  have h2 := h.2.2.1 (-q) (-y) (by linarith) (by linarith) (by simpa using hA)
  simpa using h2

theorem isUpDown_false : IsUpDown fun _ => False := ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- **A threshold event by countable conditions.** If `H` (alive before the stop) has the order shape and kills `0`,
and `AT` (alive at the stop) has the order shape, then some point of `(a, ∞)` is mapped by `m` to a hit value
(`H ∧ ¬ AT`) iff a rational or one of the candidates `posInf AT`, `negSup AT` is a hit value above some value of
`m`. -/
theorem exists_hit_iff (hm : RightGood m a) {H AT : ℝ → Prop} (hH0 : ¬ H 0) (hH : IsUpDown H)
    (hT : IsUpDown AT) :
    (∃ x, a < x ∧ H (m x) ∧ ¬ AT (m x)) ↔
      (∃ q : ℚ, (∃ x, a < x ∧ m x < q) ∧ H q ∧ ¬ AT q) ∨
      ((∃ x, a < x ∧ m x < posInf AT) ∧ H (posInf AT) ∧ ¬ AT (posInf AT)) ∨
      ((∃ x, a < x ∧ m x < negSup AT) ∧ H (negSup AT) ∧ ¬ AT (negSup AT)) := by
  constructor
  · rintro ⟨x, hx, hHx, hATx⟩
    obtain ⟨x', hx', hx'y⟩ := (exists_eq_iff_exists_lt hm).1 ⟨x, hx, rfl⟩
    by_cases hq : ∃ q : ℚ, (∃ x, a < x ∧ m x < q) ∧ H q ∧ ¬ AT q
    · exact Or.inl hq
    push Not at hq
    set y := m x with hy
    rcases lt_trichotomy y 0 with hneg | hzero | hpos
    · -- a negative hit value is the candidate `negSup AT`
      refine Or.inr (Or.inr ?_)
      have hbdd : BddAbove {z | z < 0 ∧ AT z} := ⟨0, fun _ hz => hz.1.le⟩
      have hne : {z | z < 0 ∧ AT z}.Nonempty := by
        by_contra hemp
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hx'y (show y - 1 < y by linarith))
        have hqy : (q : ℝ) < y := hq2
        exact hemp ⟨q, hqy.trans hneg, hq q ⟨x', hx', (le_max_left _ _).trans_lt hq1⟩ (hH.2 y q hqy hneg hHx)⟩
      have h1 : negSup AT ≤ y := csSup_le hne fun z hz => by
        by_contra hzy
        push Not at hzy
        exact hATx (hT.2 z y hzy hz.1 hz.2)
      have h2 : y ≤ negSup AT := by
        by_contra hlt
        push Not at hlt
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hlt hx'y)
        have hAq := hq q ⟨x', hx', (le_max_right _ _).trans_lt hq1⟩ (hH.2 y q hq2 hneg hHx)
        have : (q : ℝ) ≤ negSup AT := le_csSup hbdd ⟨hq2.trans hneg, hAq⟩
        linarith [le_max_left (negSup AT) (m x')]
      have he : y = negSup AT := le_antisymm h2 h1
      rw [← he]
      exact ⟨⟨x', hx', hx'y⟩, hHx, hATx⟩
    · exact absurd (hzero ▸ hHx) hH0
    · -- a positive hit value is the candidate `posInf AT`
      refine Or.inr (Or.inl ?_)
      have hne : {z | 0 < z ∧ AT z}.Nonempty := by
        by_contra hemp
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + 1 by linarith)
        exact hemp ⟨q, hpos.trans hq1, hq q ⟨x', hx', hx'y.trans hq1⟩ (hH.1 y q hpos hq1 hHx)⟩
      have h1 : y ≤ posInf AT := le_csInf hne fun z hz => by
        by_contra hzy
        push Not at hzy
        exact hATx (hT.1 z y hz.1 hzy hz.2)
      have h2 : posInf AT ≤ y := by
        by_contra hlt
        push Not at hlt
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
        exact not_alive_of_lt_posInf (hpos.trans hq1) hq2 (hq q ⟨x', hx', hx'y.trans hq1⟩ (hH.1 y q hpos hq1 hHx))
      have he : y = posInf AT := le_antisymm h1 h2
      rw [← he]
      exact ⟨⟨x', hx', hx'y⟩, hHx, hATx⟩
  · rintro (⟨q, hq, hHq, hATq⟩ | ⟨hc, hHc, hATc⟩ | ⟨hc, hHc, hATc⟩)
    · obtain ⟨x, hx, hxq⟩ := (exists_eq_iff_exists_lt hm).2 hq
      exact ⟨x, hx, hxq ▸ hHq, hxq ▸ hATq⟩
    · obtain ⟨x, hx, hxq⟩ := (exists_eq_iff_exists_lt hm).2 hc
      exact ⟨x, hx, hxq ▸ hHc, hxq ▸ hATc⟩
    · obtain ⟨x, hx, hxq⟩ := (exists_eq_iff_exists_lt hm).2 hc
      exact ⟨x, hx, hxq ▸ hHc, hxq ▸ hATc⟩

end Hit

end StagedLaw

end Exist

end InteractingSLE
