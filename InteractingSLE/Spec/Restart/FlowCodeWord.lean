/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Datum
import InteractingSLE.Spec.Exist.StagedKernel
import InteractingSLE.GFF.PushforwardMeas
import InteractingSLE.Spec.Sec4.Prob41Flow

/-!
# The flow-line force word of a boundary word is Borel in the word and the seed

Packet PROVE-CONDDET. A canonical flow code (`Restart.IsFlowCode`) must be jointly measurable in the boundary word `c`,
the seed `x` and the field. The flow line of a field with data `c` from `x` is the coupling of the **flow-line force
word** (`flowLineXL c.fn c.jumps x`, …, `flowLineRhoR κ c.fn c.jumps x θ`), whose numbers of marks depend on `(c, x)`.
This file makes that word a measurable datum, in the padded form used by the staged driver
(`Exist.Staged.PadWord`, `Exist.Staged.truncWord`, `Exist.Staged.stagedDrv`), and the flow-field chart jointly
measurable in the seed.

* `card_filter_image_eq`, `measurable_card_filter_image`: the number of distinct values among `p 0, …, p (n-1)` with
  a property is the number of first occurrences with it, hence measurable in the parameters;
* `orderEmbOfFin_le_iff`, `measurable_orderStat`: the `k`-th smallest element of such a finite set is `≤ t` iff at
  least `k + 1` of its elements are `≤ t`, hence measurable;
* `BoundaryWord.leftLim_fn`, `BoundaryWord.rightLim_fn`: the one-sided limits of `c.fn` are `q (index y)` and
  `q (indexLE y)`;
* **`measurable_flowLineNL`**, **`measurable_flowLineNR`**, **`measurable_flowPad`**, **`truncWord_flowPad`**: the
  numbers of marks and the padded word data of the flow-line word are measurable in `(c, x)`, and truncating the padded
  data gives the flow-line word back;
* **`measurable_flowField_uncurry`**: `(x, f) ↦ flowField x a f` is measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### Counting distinct values -/

section Count

/-- The distinct values among `p 0, …, p (n-1)` satisfying `Q` are counted by their first occurrences. -/
theorem card_filter_image_eq (n : ℕ) (p : ℕ → ℝ) (Q : ℝ → Prop) [DecidablePred Q] :
    (((Finset.range n).image p).filter Q).card =
      ((Finset.range n).filter fun i => Q (p i) ∧ ∀ j < i, p j ≠ p i).card := by
  classical
  have e : ((Finset.range n).image p).filter Q =
      ((Finset.range n).filter fun i => Q (p i) ∧ ∀ j < i, p j ≠ p i).image p := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hQ⟩
      have hex : ∃ j, j < n ∧ p j = p i := ⟨i, hi, rfl⟩
      have hj : Nat.find hex < n ∧ p (Nat.find hex) = p i := Nat.find_spec hex
      refine ⟨Nat.find hex, ⟨hj.1, by rw [hj.2]; exact hQ, fun l hl he => ?_⟩, hj.2⟩
      exact Nat.find_min hex hl ⟨hl.trans hj.1, he.trans hj.2⟩
    · rintro ⟨i, ⟨hi, hQ, -⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, hQ⟩
  rw [e, Finset.card_image_of_injOn]
  intro i hi j hj hij
  simp only [Finset.coe_filter, Finset.mem_range, mem_ofPred_eq] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hj.2.2 i h hij
  · exact hi.2.2 j h hij.symm

variable {α : Type*} [MeasurableSpace α]

/-- The number of distinct values with a measurable property among measurably many measurable values. -/
theorem measurable_card_filter_image {n : α → ℕ} (hn : Measurable n) {p : ℕ → α → ℝ}
    (hp : ∀ i, Measurable (p i)) {Q : α → ℝ → Prop} [∀ a, DecidablePred (Q a)]
    (hQ : ∀ i, MeasurableSet {a | Q a (p i a)}) :
    Measurable fun a => (((Finset.range (n a)).image fun i => p i a).filter (Q a)).card := by
  classical
  have hI : ∀ i, Measurable fun a =>
      if Q a (p i a) ∧ ∀ j < i, p j a ≠ p i a then (1 : ℕ) else 0 := by
    intro i
    refine Measurable.ite ?_ measurable_const measurable_const
    have e : {a | Q a (p i a) ∧ ∀ j < i, p j a ≠ p i a} =
        {a | Q a (p i a)} ∩ ⋂ j ∈ Finset.range i, {a | p j a = p i a}ᶜ := by
      ext a
      simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_range, mem_compl_iff]
    rw [e]
    exact (hQ i).inter (Finset.measurableSet_biInter _ fun j _ => (measurableSet_eq_fun (hp j) (hp i)).compl)
  have hS : Measurable fun q : α × ℕ => ∑ i ∈ Finset.range q.2,
      (if Q q.1 (p i q.1) ∧ ∀ j < i, p j q.1 ≠ p i q.1 then (1 : ℕ) else 0) :=
    measurable_from_prod_countable_left fun m => by
      dsimp only
      exact Finset.measurable_sum _ fun i _ => hI i
  have e : (fun a => (((Finset.range (n a)).image fun i => p i a).filter (Q a)).card) = fun a =>
      ∑ i ∈ Finset.range (n a), (if Q a (p i a) ∧ ∀ j < i, p j a ≠ p i a then (1 : ℕ) else 0) := by
    funext a
    rw [card_filter_image_eq, Finset.card_filter]
  rw [e]
  exact hS.comp (measurable_id.prodMk hn)

end Count

/-! ### Order statistics -/

section Order

/-- The `k`-th smallest element of a finite set of reals is `≤ t` iff at least `k + 1` of its elements are. -/
theorem orderEmbOfFin_le_iff {s : Finset ℝ} {N : ℕ} (h : s.card = N) (k : Fin N) (t : ℝ) :
    s.orderEmbOfFin h k ≤ t ↔ (k : ℕ) + 1 ≤ (s.filter (· ≤ t)).card := by
  classical
  set e := s.orderEmbOfFin h with he
  have hfil : s.filter (· ≤ t) = (Finset.univ.filter fun j : Fin N => e j ≤ t).map e.toEmbedding := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, hyt⟩
      have hr : y ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hy
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, hyt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s h j, hj⟩
  rw [hfil, Finset.card_map]
  constructor
  · intro hk
    calc (k : ℕ) + 1 = (Finset.Iic k).card := (Fin.card_Iic k).symm
      _ ≤ _ := Finset.card_le_card fun j hj => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (e.monotone (Finset.mem_Iic.1 hj)).trans hk
  · intro hk
    by_contra hlt
    have hlt : t < e k := not_le.1 hlt
    have hsub : (Finset.univ.filter fun j : Fin N => e j ≤ t) ⊆ Finset.Iio k := fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [Finset.mem_Iio]
      by_contra hjk
      have hjk : k ≤ j := not_lt.1 hjk
      exact absurd (hlt.trans_le (e.monotone hjk)) (not_lt.2 hj)
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h1
    omega

variable {α : Type*} [MeasurableSpace α]

/-- The finite set of distinct values with property `Q`. -/
def valSet (n : α → ℕ) (p : ℕ → α → ℝ) (Q : α → ℝ → Prop) [∀ a, DecidablePred (Q a)] (a : α) : Finset ℝ :=
  ((Finset.range (n a)).image fun i => p i a).filter (Q a)

/-- The `k`-th smallest element of `valSet`, `0` if there is none. -/
def orderStat (n : α → ℕ) (p : ℕ → α → ℝ) (Q : α → ℝ → Prop) [∀ a, DecidablePred (Q a)] (k : ℕ) (a : α) : ℝ :=
  if h : k < (valSet n p Q a).card then (valSet n p Q a).orderEmbOfFin rfl ⟨k, h⟩ else 0

theorem measurable_card_valSet {n : α → ℕ} (hn : Measurable n) {p : ℕ → α → ℝ} (hp : ∀ i, Measurable (p i))
    {Q : α → ℝ → Prop} [∀ a, DecidablePred (Q a)] (hQ : ∀ i, MeasurableSet {a | Q a (p i a)}) :
    Measurable fun a => (valSet n p Q a).card :=
  measurable_card_filter_image hn hp hQ

/-- **The order statistics of `valSet` are measurable.** -/
theorem measurable_orderStat {n : α → ℕ} (hn : Measurable n) {p : ℕ → α → ℝ} (hp : ∀ i, Measurable (p i))
    {Q : α → ℝ → Prop} [∀ a, DecidablePred (Q a)] (hQ : ∀ i, MeasurableSet {a | Q a (p i a)}) (k : ℕ) :
    Measurable (orderStat n p Q k) := by
  classical
  have hc := measurable_card_valSet hn hp hQ
  refine measurable_of_Iic fun t => ?_
  have hct : Measurable fun a => ((valSet n p Q a).filter (· ≤ t)).card := by
    have e : (fun a => ((valSet n p Q a).filter (· ≤ t)).card) = fun a =>
        (((Finset.range (n a)).image fun i => p i a).filter fun y => Q a y ∧ y ≤ t).card := by
      funext a
      rw [valSet, Finset.filter_filter]
    rw [e]
    exact measurable_card_filter_image hn hp fun i => (hQ i).inter (measurableSet_le (hp i) measurable_const)
  have e : orderStat n p Q k ⁻¹' Iic t =
      ({a | k < (valSet n p Q a).card} ∩ {a | k + 1 ≤ ((valSet n p Q a).filter (· ≤ t)).card}) ∪
        ({a | ¬ k < (valSet n p Q a).card} ∩ {_a | (0 : ℝ) ≤ t}) := by
    ext a
    simp only [mem_preimage, mem_Iic, orderStat, mem_union, mem_inter_iff, mem_ofPred_eq]
    by_cases hk : k < (valSet n p Q a).card
    · simp only [hk, ↓reduceDIte, not_true_eq_false, false_and, or_false, true_and]
      exact orderEmbOfFin_le_iff rfl ⟨k, hk⟩ t
    · simp only [hk, ↓reduceDIte, false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  refine ((hc MeasurableSet.of_discrete).inter (hct MeasurableSet.of_discrete)).union
    ((hc (MeasurableSet.of_discrete (s := {m : ℕ | ¬ k < m}))).inter (MeasurableSet.const ((0 : ℝ) ≤ t)))

omit [MeasurableSpace α] in
/-- On `valSet`, `orderStat` is the order embedding. -/
theorem orderStat_eq {n : α → ℕ} {p : ℕ → α → ℝ} {Q : α → ℝ → Prop} [∀ a, DecidablePred (Q a)] {a : α}
    (k : Fin (valSet n p Q a).card) : orderStat n p Q k a = (valSet n p Q a).orderEmbOfFin rfl k := by
  simp only [orderStat, k.2, ↓reduceDIte]

end Order

/-! ### Counting positions -/

section Index

variable {α : Type*} [MeasurableSpace α]

/-- A count over `range (n a)` of a measurable property is measurable. -/
theorem measurable_card_range_filter {n : α → ℕ} (hn : Measurable n) {P : ℕ → α → Prop}
    [∀ i a, Decidable (P i a)] (hP : ∀ i, MeasurableSet {a | P i a}) :
    Measurable fun a => ((Finset.range (n a)).filter fun i => P i a).card := by
  have hS : Measurable fun r : α × ℕ => ∑ i ∈ Finset.range r.2, (if P i r.1 then (1 : ℕ) else 0) :=
    measurable_from_prod_countable_left fun m => by
      dsimp only
      exact Finset.measurable_sum _ fun i _ => Measurable.ite (hP i) measurable_const measurable_const
  have e : (fun a => ((Finset.range (n a)).filter fun i => P i a).card) = fun a =>
      ∑ i ∈ Finset.range (n a), (if P i a then (1 : ℕ) else 0) := by
    funext a
    rw [Finset.card_filter]
  rw [e]
  exact hS.comp (measurable_id.prodMk hn)

/-- Reading a height of a measurable word at a measurable index. -/
theorem measurable_height {c : α → BoundaryWord} (hc : Measurable c) {k : α → ℕ} (hk : Measurable k) :
    Measurable fun a => (c a).2.2 (k a) := by
  have h : Measurable fun r : α × ℕ => (c r.1).2.2 r.2 :=
    measurable_from_prod_countable_left fun m => by
      dsimp only
      exact (measurable_pi_apply m).comp (measurable_snd.comp (measurable_snd.comp hc))
  exact h.comp (measurable_id.prodMk hk)

end Index

namespace BoundaryWord

/-- The number of jump positions at or left of `y`. -/
def indexLE (c : BoundaryWord) (y : ℝ) : ℕ := ((Finset.range c.1).filter fun i => c.2.1 i ≤ y).card

theorem measurable_position (i : ℕ) : Measurable fun c : BoundaryWord => c.2.1 i :=
  (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)

theorem measurable_index : Measurable fun q : BoundaryWord × ℝ => q.1.index q.2 :=
  measurable_card_range_filter (measurable_fst.comp measurable_fst) fun i =>
    measurableSet_lt ((measurable_position i).comp measurable_fst) measurable_snd

theorem measurable_indexLE : Measurable fun q : BoundaryWord × ℝ => q.1.indexLE q.2 :=
  measurable_card_range_filter (measurable_fst.comp measurable_fst) fun i =>
    measurableSet_le ((measurable_position i).comp measurable_fst) measurable_snd

/-- Finitely many positions left of `y` lie below some `a < y`. -/
theorem exists_lt_bound (c : BoundaryWord) (y : ℝ) : ∃ a < y, ∀ i < c.1, c.2.1 i < y → c.2.1 i ≤ a := by
  have key : ∀ s : Finset ℕ, ∃ a < y, ∀ i ∈ s, c.2.1 i < y → c.2.1 i ≤ a := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨y - 1, by linarith, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert j s _ ih =>
      obtain ⟨a, ha, hb⟩ := ih
      by_cases hjy : c.2.1 j < y
      · refine ⟨max a (c.2.1 j), max_lt ha hjy, fun i hi hiy => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact le_max_right _ _
        · exact (hb i hi hiy).trans (le_max_left _ _)
      · refine ⟨a, ha, fun i hi hiy => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact absurd hiy hjy
        · exact hb i hi hiy
  obtain ⟨a, ha, hb⟩ := key (Finset.range c.1)
  exact ⟨a, ha, fun i hi => hb i (Finset.mem_range.2 hi)⟩

/-- Finitely many positions right of `y` lie above some `b > y`. -/
theorem exists_gt_bound (c : BoundaryWord) (y : ℝ) : ∃ b > y, ∀ i < c.1, y < c.2.1 i → b ≤ c.2.1 i := by
  have key : ∀ s : Finset ℕ, ∃ b > y, ∀ i ∈ s, y < c.2.1 i → b ≤ c.2.1 i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨y + 1, by linarith, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert j s _ ih =>
      obtain ⟨b, hb, hbb⟩ := ih
      by_cases hjy : y < c.2.1 j
      · refine ⟨min b (c.2.1 j), lt_min hb hjy, fun i hi hiy => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hbb i hi hiy)
      · refine ⟨b, hb, fun i hi hiy => ?_⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact absurd hiy hjy
        · exact hbb i hi hiy
  obtain ⟨b, hb, hbb⟩ := key (Finset.range c.1)
  exact ⟨b, hb, fun i hi => hbb i (Finset.mem_range.2 hi)⟩

/-- **The left limit of a word's boundary function**: the height after the positions strictly left of `y`. -/
theorem leftLim_fn (c : BoundaryWord) (y : ℝ) : leftLim c.fn y = c.2.2 (c.index y) := by
  obtain ⟨a, hay, ha⟩ := c.exists_lt_bound y
  refine Sec4.leftLim_eq_of_forall hay fun t ht => ?_
  have e : ((Finset.range c.1).filter fun i => c.2.1 i < t) = (Finset.range c.1).filter fun i => c.2.1 i < y :=
    Finset.filter_congr fun i hi =>
      ⟨fun h => h.trans ht.2, fun h => (ha i (Finset.mem_range.1 hi) h).trans_lt ht.1⟩
  simp only [fn, index, e]

/-- **The right limit of a word's boundary function**: the height after the positions at or left of `y`. -/
theorem rightLim_fn (c : BoundaryWord) (y : ℝ) : rightLim c.fn y = c.2.2 (c.indexLE y) := by
  obtain ⟨b, hyb, hb⟩ := c.exists_gt_bound y
  refine Sec4.rightLim_eq_of_forall hyb fun t ht => ?_
  have e : ((Finset.range c.1).filter fun i => c.2.1 i < t) = (Finset.range c.1).filter fun i => c.2.1 i ≤ y :=
    Finset.filter_congr fun i hi =>
      ⟨fun h => not_lt.1 fun hy => lt_asymm h (ht.2.trans_le (hb i (Finset.mem_range.1 hi) hy)),
        fun h => h.trans_lt ht.1⟩
  simp only [fn, index, indexLE, e]

theorem measurable_leftLim : Measurable fun q : BoundaryWord × ℝ => leftLim q.1.fn q.2 := by
  simp_rw [leftLim_fn]
  exact measurable_height measurable_fst measurable_index

theorem measurable_rightLim : Measurable fun q : BoundaryWord × ℝ => rightLim q.1.fn q.2 := by
  simp_rw [rightLim_fn]
  exact measurable_height measurable_fst measurable_indexLE

end BoundaryWord

/-! ### The flow-line word as a measurable datum -/

section FlowWord

open BoundaryWord

/-- The genuine jumps strictly left of the seed, as a `valSet`. -/
def leftJumpPred (a : BoundaryWord × ℝ) (y : ℝ) : Prop := leftLim a.1.fn y ≠ rightLim a.1.fn y ∧ y < a.2

/-- The genuine jumps strictly right of the seed, as a `valSet`. -/
def rightJumpPred (a : BoundaryWord × ℝ) (y : ℝ) : Prop := leftLim a.1.fn y ≠ rightLim a.1.fn y ∧ a.2 < y

open Classical in
/-- The genuine jumps of `c.fn` strictly left of `x`. -/
def leftJumps (a : BoundaryWord × ℝ) : Finset ℝ :=
  valSet (fun a : BoundaryWord × ℝ => a.1.1) (fun i a => a.1.2.1 i) leftJumpPred a

open Classical in
/-- The genuine jumps of `c.fn` strictly right of `x`. -/
def rightJumps (a : BoundaryWord × ℝ) : Finset ℝ :=
  valSet (fun a : BoundaryWord × ℝ => a.1.1) (fun i a => a.1.2.1 i) rightJumpPred a

theorem filter_jumpSet_lt_eq (a : BoundaryWord × ℝ) :
    (jumpSet a.1.fn a.1.jumps).filter (· < a.2) = leftJumps a := by
  classical
  ext y
  simp only [jumpSet, BoundaryWord.jumps, leftJumps, valSet, leftJumpPred, Finset.mem_filter]
  tauto

theorem filter_jumpSet_gt_eq (a : BoundaryWord × ℝ) :
    (jumpSet a.1.fn a.1.jumps).filter (a.2 < ·) = rightJumps a := by
  classical
  ext y
  simp only [jumpSet, BoundaryWord.jumps, rightJumps, valSet, rightJumpPred, Finset.mem_filter]
  tauto

theorem measurableSet_leftJumpPred (i : ℕ) :
    MeasurableSet {a : BoundaryWord × ℝ | leftJumpPred a (a.1.2.1 i)} := by
  have hp : Measurable fun a : BoundaryWord × ℝ => (a.1, a.1.2.1 i) :=
    measurable_fst.prodMk ((measurable_position i).comp measurable_fst)
  exact (measurableSet_eq_fun (measurable_leftLim.comp hp) (measurable_rightLim.comp hp)).compl.inter
    (measurableSet_lt ((measurable_position i).comp measurable_fst) measurable_snd)

theorem measurableSet_rightJumpPred (i : ℕ) :
    MeasurableSet {a : BoundaryWord × ℝ | rightJumpPred a (a.1.2.1 i)} := by
  have hp : Measurable fun a : BoundaryWord × ℝ => (a.1, a.1.2.1 i) :=
    measurable_fst.prodMk ((measurable_position i).comp measurable_fst)
  exact (measurableSet_eq_fun (measurable_leftLim.comp hp) (measurable_rightLim.comp hp)).compl.inter
    (measurableSet_lt measurable_snd ((measurable_position i).comp measurable_fst))

theorem flowLineNL_eq (a : BoundaryWord × ℝ) : flowLineNL a.1.fn a.1.jumps a.2 = (leftJumps a).card + 1 := by
  rw [flowLineNL, filter_jumpSet_lt_eq]

theorem flowLineNR_eq (a : BoundaryWord × ℝ) : flowLineNR a.1.fn a.1.jumps a.2 = (rightJumps a).card + 1 := by
  rw [flowLineNR, filter_jumpSet_gt_eq]

theorem measurable_card_leftJumps : Measurable fun a : BoundaryWord × ℝ => (leftJumps a).card := by
  classical
  exact measurable_card_valSet (measurable_fst.comp measurable_fst)
    (fun i => (measurable_position i).comp measurable_fst) measurableSet_leftJumpPred

theorem measurable_card_rightJumps : Measurable fun a : BoundaryWord × ℝ => (rightJumps a).card := by
  classical
  exact measurable_card_valSet (measurable_fst.comp measurable_fst)
    (fun i => (measurable_position i).comp measurable_fst) measurableSet_rightJumpPred

/-- **The number of left marks of the flow-line word is measurable in `(c, x)`.** -/
theorem measurable_flowLineNL : Measurable fun a : BoundaryWord × ℝ => flowLineNL a.1.fn a.1.jumps a.2 := by
  simp_rw [flowLineNL_eq]
  exact measurable_card_leftJumps.add_const 1

/-- **The number of right marks of the flow-line word is measurable in `(c, x)`.** -/
theorem measurable_flowLineNR : Measurable fun a : BoundaryWord × ℝ => flowLineNR a.1.fn a.1.jumps a.2 := by
  simp_rw [flowLineNR_eq]
  exact measurable_card_rightJumps.add_const 1

theorem orderEmbOfFin_congr {s t : Finset ℝ} (e : s = t) (k : Fin s.card) :
    s.orderEmbOfFin rfl k = t.orderEmbOfFin rfl (Fin.cast (congrArg Finset.card e) k) := by
  subst e
  rfl

open Classical in
/-- The `k`-th smallest genuine jump strictly left of the seed. -/
def leftStat (k : ℕ) (a : BoundaryWord × ℝ) : ℝ :=
  orderStat (fun a : BoundaryWord × ℝ => a.1.1) (fun i a => a.1.2.1 i) leftJumpPred k a

open Classical in
/-- The `k`-th smallest genuine jump strictly right of the seed. -/
def rightStat (k : ℕ) (a : BoundaryWord × ℝ) : ℝ :=
  orderStat (fun a : BoundaryWord × ℝ => a.1.1) (fun i a => a.1.2.1 i) rightJumpPred k a

theorem measurable_leftStat_uncurry : Measurable fun q : (BoundaryWord × ℝ) × ℕ => leftStat q.2 q.1 := by
  classical
  refine measurable_from_prod_countable_left fun k => ?_
  exact measurable_orderStat (measurable_fst.comp measurable_fst)
    (fun i => (measurable_position i).comp measurable_fst) measurableSet_leftJumpPred k

theorem measurable_rightStat_uncurry : Measurable fun q : (BoundaryWord × ℝ) × ℕ => rightStat q.2 q.1 := by
  classical
  refine measurable_from_prod_countable_left fun k => ?_
  exact measurable_orderStat (measurable_fst.comp measurable_fst)
    (fun i => (measurable_position i).comp measurable_fst) measurableSet_rightJumpPred k

/-- The left marks of the flow-line word, read off in decreasing order, are order statistics. -/
theorem orderEmb_left_rev (a : BoundaryWord × ℝ) {m : ℕ}
    (hm : m < ((jumpSet a.1.fn a.1.jumps).filter (· < a.2)).card) :
    ((jumpSet a.1.fn a.1.jumps).filter (· < a.2)).orderEmbOfFin rfl (Fin.rev ⟨m, hm⟩) =
      leftStat ((leftJumps a).card - (m + 1)) a := by
  classical
  have hc : ((jumpSet a.1.fn a.1.jumps).filter (· < a.2)).card = (leftJumps a).card := by
    rw [filter_jumpSet_lt_eq]
  rw [orderEmbOfFin_congr (filter_jumpSet_lt_eq a)]
  have hk : ((Fin.cast (congrArg Finset.card (filter_jumpSet_lt_eq a)) (Fin.rev ⟨m, hm⟩) :
      Fin (leftJumps a).card) : ℕ) = (leftJumps a).card - (m + 1) := by
    simp only [Fin.val_cast, Fin.val_rev, hc]
  rw [← hk]
  exact (orderStat_eq (Fin.cast (congrArg Finset.card (filter_jumpSet_lt_eq a)) (Fin.rev ⟨m, hm⟩))).symm

/-- The right marks of the flow-line word, read off in increasing order, are order statistics. -/
theorem orderEmb_right (a : BoundaryWord × ℝ) {m : ℕ}
    (hm : m < ((jumpSet a.1.fn a.1.jumps).filter (a.2 < ·)).card) :
    ((jumpSet a.1.fn a.1.jumps).filter (a.2 < ·)).orderEmbOfFin rfl ⟨m, hm⟩ = rightStat m a := by
  classical
  rw [orderEmbOfFin_congr (filter_jumpSet_gt_eq a)]
  exact (orderStat_eq (Fin.cast (congrArg Finset.card (filter_jumpSet_gt_eq a)) ⟨m, hm⟩)).symm

/-- **The flow-line word in padded form**: positions and weights indexed by `ℕ`, `0` beyond the numbers of marks. -/
def flowPad (κ θ : ℝ) (a : BoundaryWord × ℝ) : Exist.Staged.PadWord :=
  (((fun i => if h : i < flowLineNL a.1.fn a.1.jumps a.2 then flowLineXL a.1.fn a.1.jumps a.2 ⟨i, h⟩ else 0),
      fun j => if h : j < flowLineNR a.1.fn a.1.jumps a.2 then flowLineXR a.1.fn a.1.jumps a.2 ⟨j, h⟩ else 0),
    ((fun i => if h : i < flowLineNL a.1.fn a.1.jumps a.2 then
        flowLineRhoL κ a.1.fn a.1.jumps a.2 θ ⟨i, h⟩ else 0),
      fun j => if h : j < flowLineNR a.1.fn a.1.jumps a.2 then
        flowLineRhoR κ a.1.fn a.1.jumps a.2 θ ⟨j, h⟩ else 0))

/-- **Truncating the padded data gives the flow-line word.** -/
theorem truncWord_flowPad (κ θ : ℝ) (a : BoundaryWord × ℝ) :
    Exist.Staged.truncWord (flowLineNL a.1.fn a.1.jumps a.2) (flowLineNR a.1.fn a.1.jumps a.2) (flowPad κ θ a) =
      ((flowLineXL a.1.fn a.1.jumps a.2, flowLineXR a.1.fn a.1.jumps a.2),
        (flowLineRhoL κ a.1.fn a.1.jumps a.2 θ, flowLineRhoR κ a.1.fn a.1.jumps a.2 θ)) := by
  simp only [Exist.Staged.truncWord, flowPad, Fin.is_lt, ↓reduceDIte, Fin.eta]

theorem measurableSet_lt_card_leftJumps (m : ℕ) : MeasurableSet {a : BoundaryWord × ℝ | m < (leftJumps a).card} :=
  measurable_card_leftJumps (MeasurableSet.of_discrete (s := {n : ℕ | m < n}))

theorem measurableSet_lt_card_rightJumps (m : ℕ) :
    MeasurableSet {a : BoundaryWord × ℝ | m < (rightJumps a).card} :=
  measurable_card_rightJumps (MeasurableSet.of_discrete (s := {n : ℕ | m < n}))

/-- The `(m+1)`-th left mark (from the seed outwards) as a measurable function. -/
theorem measurable_leftStat_rev (m : ℕ) :
    Measurable fun a : BoundaryWord × ℝ => leftStat ((leftJumps a).card - (m + 1)) a :=
  measurable_leftStat_uncurry.comp (measurable_id.prodMk
    ((measurable_from_nat (f := fun n : ℕ => n - (m + 1))).comp measurable_card_leftJumps))

theorem measurable_rightStat (m : ℕ) : Measurable fun a : BoundaryWord × ℝ => rightStat m a :=
  measurable_rightStat_uncurry.comp (measurable_id.prodMk measurable_const)

theorem flowPad_XL_succ (κ θ : ℝ) (a : BoundaryWord × ℝ) (m : ℕ) :
    (flowPad κ θ a).1.1 (m + 1) =
      if m < (leftJumps a).card then leftStat ((leftJumps a).card - (m + 1)) a - a.2 else 0 := by
  have hNL := flowLineNL_eq a
  by_cases hm : m < (leftJumps a).card
  · have h1 : m + 1 < flowLineNL a.1.fn a.1.jumps a.2 := by omega
    have hm' : m < ((jumpSet a.1.fn a.1.jumps).filter (· < a.2)).card := by
      rw [filter_jumpSet_lt_eq]; exact hm
    simp only [flowPad, h1, ↓reduceDIte, hm, ↓reduceIte]
    rw [← orderEmb_left_rev a hm']
    rfl
  · have h1 : ¬ m + 1 < flowLineNL a.1.fn a.1.jumps a.2 := by omega
    simp only [flowPad, h1, ↓reduceDIte, hm, ↓reduceIte]

theorem flowPad_RhoL_succ (κ θ : ℝ) (a : BoundaryWord × ℝ) (m : ℕ) :
    (flowPad κ θ a).2.1 (m + 1) =
      if m < (leftJumps a).card then
        (rightLim a.1.fn (leftStat ((leftJumps a).card - (m + 1)) a) -
          leftLim a.1.fn (leftStat ((leftJumps a).card - (m + 1)) a)) / sleLambda κ else 0 := by
  have hNL := flowLineNL_eq a
  by_cases hm : m < (leftJumps a).card
  · have h1 : m + 1 < flowLineNL a.1.fn a.1.jumps a.2 := by omega
    have hm' : m < ((jumpSet a.1.fn a.1.jumps).filter (· < a.2)).card := by
      rw [filter_jumpSet_lt_eq]; exact hm
    simp only [flowPad, h1, ↓reduceDIte, hm, ↓reduceIte]
    rw [← orderEmb_left_rev a hm']
    rfl
  · have h1 : ¬ m + 1 < flowLineNL a.1.fn a.1.jumps a.2 := by omega
    simp only [flowPad, h1, ↓reduceDIte, hm, ↓reduceIte]

theorem flowPad_XR_succ (κ θ : ℝ) (a : BoundaryWord × ℝ) (m : ℕ) :
    (flowPad κ θ a).1.2 (m + 1) = if m < (rightJumps a).card then rightStat m a - a.2 else 0 := by
  have hNR := flowLineNR_eq a
  by_cases hm : m < (rightJumps a).card
  · have h1 : m + 1 < flowLineNR a.1.fn a.1.jumps a.2 := by omega
    have hm' : m < ((jumpSet a.1.fn a.1.jumps).filter (a.2 < ·)).card := by
      rw [filter_jumpSet_gt_eq]; exact hm
    simp only [flowPad, h1, ↓reduceDIte, hm, ↓reduceIte]
    rw [← orderEmb_right a hm']
    rfl
  · have h1 : ¬ m + 1 < flowLineNR a.1.fn a.1.jumps a.2 := by omega
    simp only [flowPad, h1, ↓reduceDIte, hm, ↓reduceIte]

theorem flowPad_RhoR_succ (κ θ : ℝ) (a : BoundaryWord × ℝ) (m : ℕ) :
    (flowPad κ θ a).2.2 (m + 1) =
      if m < (rightJumps a).card then
        (rightLim a.1.fn (rightStat m a) - leftLim a.1.fn (rightStat m a)) / sleLambda κ else 0 := by
  have hNR := flowLineNR_eq a
  by_cases hm : m < (rightJumps a).card
  · have h1 : m + 1 < flowLineNR a.1.fn a.1.jumps a.2 := by omega
    have hm' : m < ((jumpSet a.1.fn a.1.jumps).filter (a.2 < ·)).card := by
      rw [filter_jumpSet_gt_eq]; exact hm
    simp only [flowPad, h1, ↓reduceDIte, hm, ↓reduceIte]
    rw [← orderEmb_right a hm']
    rfl
  · have h1 : ¬ m + 1 < flowLineNR a.1.fn a.1.jumps a.2 := by omega
    simp only [flowPad, h1, ↓reduceDIte, hm, ↓reduceIte]

theorem flowPad_zero (κ θ : ℝ) (a : BoundaryWord × ℝ) :
    (flowPad κ θ a).1.1 0 = 0 ∧ (flowPad κ θ a).1.2 0 = 0 ∧
      (flowPad κ θ a).2.1 0 =
        -(leftLim a.1.fn a.2 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 ∧
      (flowPad κ θ a).2.2 0 = (rightLim a.1.fn a.2 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  have h1 : 0 < flowLineNL a.1.fn a.1.jumps a.2 := by rw [flowLineNL_eq]; omega
  have h2 : 0 < flowLineNR a.1.fn a.1.jumps a.2 := by rw [flowLineNR_eq]; omega
  simp only [flowPad, h1, h2, ↓reduceDIte]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The padded flow-line word is measurable in `(c, x)`.** -/
theorem measurable_flowPad (κ θ : ℝ) : Measurable (flowPad κ θ) := by
  have hcoord : ∀ (g : Exist.Staged.PadWord → ℕ → ℝ), (∀ i, Measurable fun p => g p i) →
      (∀ i, Measurable fun a => g (flowPad κ θ a) i) → Measurable fun a => g (flowPad κ θ a) := fun g _ h =>
    measurable_pi_iff.2 h
  have hm : ∀ m : ℕ, Measurable fun a : BoundaryWord × ℝ => (a.1, leftStat ((leftJumps a).card - (m + 1)) a) :=
    fun m => measurable_fst.prodMk (measurable_leftStat_rev m)
  have hm' : ∀ m : ℕ, Measurable fun a : BoundaryWord × ℝ => (a.1, rightStat m a) :=
    fun m => measurable_fst.prodMk (measurable_rightStat m)
  have hXL : Measurable fun a => (flowPad κ θ a).1.1 := by
    refine measurable_pi_iff.2 fun i => ?_
    cases i with
    | zero => simp_rw [(flowPad_zero κ θ _).1]; exact measurable_const
    | succ m =>
      simp_rw [flowPad_XL_succ]
      exact Measurable.ite (measurableSet_lt_card_leftJumps m) ((measurable_leftStat_rev m).sub measurable_snd)
        measurable_const
  have hXR : Measurable fun a => (flowPad κ θ a).1.2 := by
    refine measurable_pi_iff.2 fun i => ?_
    cases i with
    | zero => simp_rw [(flowPad_zero κ θ _).2.1]; exact measurable_const
    | succ m =>
      simp_rw [flowPad_XR_succ]
      exact Measurable.ite (measurableSet_lt_card_rightJumps m) ((measurable_rightStat m).sub measurable_snd)
        measurable_const
  have hRL : Measurable fun a => (flowPad κ θ a).2.1 := by
    refine measurable_pi_iff.2 fun i => ?_
    cases i with
    | zero =>
      simp_rw [(flowPad_zero κ θ _).2.2.1]
      exact (((measurable_leftLim.add_const _).neg).div_const _).sub_const _
    | succ m =>
      simp_rw [flowPad_RhoL_succ]
      exact Measurable.ite (measurableSet_lt_card_leftJumps m)
        (((measurable_rightLim.comp (hm m)).sub (measurable_leftLim.comp (hm m))).div_const _) measurable_const
  have hRR : Measurable fun a => (flowPad κ θ a).2.2 := by
    refine measurable_pi_iff.2 fun i => ?_
    cases i with
    | zero =>
      simp_rw [(flowPad_zero κ θ _).2.2.2]
      exact ((measurable_rightLim.add_const _).div_const _).sub_const _
    | succ m =>
      simp_rw [flowPad_RhoR_succ]
      exact Measurable.ite (measurableSet_lt_card_rightJumps m)
        (((measurable_rightLim.comp (hm' m)).sub (measurable_leftLim.comp (hm' m))).div_const _) measurable_const
  exact (hXL.prodMk hXR).prodMk (hRL.prodMk hRR)

end FlowWord

/-! ### The flow field, jointly in the seed and the field -/

/-- **`(x, f) ↦ flowField x a f` is measurable** (the shift chart recentred at a measurable seed). -/
theorem measurable_flowField_uncurry (a : ℝ) :
    Measurable fun q : ℝ × LQGMetric.DistOn upperHalfPlaneOpens => Exist.flowField q.1 a q.2 :=
  Chart.measurable_chartTransport_recenter_random' (c := fun _ => Chart.id) (fun _ => Chart.isConformal_id)
    measurable_fst (fun _ => MeasurableSet.const _) (fun _ => measurable_const.indicator (MeasurableSet.const _))
    (fun _ => measurable_const.indicator (MeasurableSet.const _)) (fun _ => continuousOn_const) measurable_snd 1 a 0

end Restart

end InteractingSLE
