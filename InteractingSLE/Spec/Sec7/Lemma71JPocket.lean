/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71IPlanar
import InteractingSLE.Spec.Sec7.Lemma71IStop
import InteractingSLE.Spec.Sec7.Lemma71EDomain
import InteractingSLE.WangWu.Prop420Ext
import InteractingSLE.WangWu.MeanIdentChamber
import InteractingSLE.Spec.Restart.ClockMeasCap
import InteractingSLE.Spec.Sec7.Lemma613

/-!
# Lemma 7.1's pocket: a measurable choice of a pocket between the outer curves

Packet PROVE-LEMMA71J, item R2 of `planning/handoffs/PROVE-LEMMA71I.md` (specification §7.1, p. 222: "Let `C` be a
connected component of `ℍ ∖ (η_{θ₁} ∪ η_{θ₂})` which lies between `η_{θ₁}` and `η_{θ₂}`").

For random outer curves `R ω` (right wall) and `L ω` (left wall), continuous for every `ω` with measurable coordinates
for a σ-algebra `m`, and an `m`-measurable event `Good` on which they are simple proper curves with a component
between them, the pocket through the first rational between-point is selected measurably:

* `measurable_range_hitting`: `ω ↦ range (R ω)` is measurable for the hitting σ-algebra;
* `measurableSet_mem_rightSideOf_relClosureH`, `measurableSet_mem_leftSideOf_relClosureH`: membership of a fixed point
  of `ℍ` in a side of the relative closure is hitting-measurable (WangWu's windows);
* `IsBetweenPt` and `measurableSet_isBetweenPt`: a fixed point is between the walls (in the relative-closure form,
  which is the frozen form for proper arcs, `isBetweenPt_iff`);
* **`exists_measurable_pocketSelection`**: an `m`-measurable index `Np` and a random open connected set `C ⊆ ℍ` with
  `m`-measurable closed-ball events, `e (Np ω) ∈ C ω` for every `ω`, `C ω` a component between the walls on `Good`
  and a fixed disc off `Good`.

With `m = σ(outer curves) ⊔ σ(Good)` this is the random pocket of `Lemma71F.Lemma71PocketPinStatement` (its
closed-ball clause); `Good` has full measure on the three-curve space (`Lemma71I.ae_isOrderedArcs`, the walls differ
by `Lemma613.lemma613ContactStatement_of_prop55`, and a chamber exists, `WangWu.nonempty_betweenComponents`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71Pin

open QuantumZipper (H)
open LocalSets Lemma71I

/-! ### Hitting-measurable random ranges and sides -/

section Hitting

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **The range of a random continuous path is hitting-measurable.** -/
theorem measurable_range_hitting {R : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (R ω))
    (hm : ∀ t, Measurable[m] fun ω => R ω t) : Measurable[m, hittingSigma] fun ω => range (R ω) := by
  refine @measurable_generateFrom Ω (Set ℂ) m _ _ fun S hS => ?_
  obtain ⟨U, hU, -, rfl⟩ := hS
  have : (fun ω => range (R ω)) ⁻¹' {A | (A ∩ U).Nonempty} = ⋃ q : ℚ≥0, {ω | R ω q ∈ U} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, htU⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.preimage (hc ω)) t htU
      obtain ⟨q, -, hq⟩ := exists_nnrat_le_dist_lt t hε
      exact ⟨q, hball (mem_ball.2 hq)⟩
    · rintro ⟨q, hq⟩
      exact ⟨_, ⟨_, rfl⟩, hq⟩
  rw [this]
  exact MeasurableSet.iUnion fun q => hm _ hU.measurableSet

/-- The union of two hitting-measurable random sets is hitting-measurable. -/
theorem measurable_union_hitting {A B : Ω → Set ℂ} (hA : Measurable[m, hittingSigma] A)
    (hB : Measurable[m, hittingSigma] B) : Measurable[m, hittingSigma] fun ω => A ω ∪ B ω := by
  refine @measurable_generateFrom Ω (Set ℂ) m _ _ fun S hS => ?_
  obtain ⟨U, hU, hUH, rfl⟩ := hS
  have : (fun ω => A ω ∪ B ω) ⁻¹' {S | (S ∩ U).Nonempty} =
      A ⁻¹' {S | (S ∩ U).Nonempty} ∪ B ⁻¹' {S | (S ∩ U).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, union_inter_distrib_right, union_nonempty]
  rw [this]
  have hmeas : MeasurableSet[hittingSigma] {S : Set ℂ | (S ∩ U).Nonempty} :=
    MeasurableSpace.measurableSet_generateFrom ⟨U, hU, hUH, rfl⟩
  exact (hA hmeas).union (hB hmeas)

/-- Membership of a point of `ℍ` in the right side of the relative closure is hitting-measurable. -/
theorem measurableSet_mem_rightSideOf_relClosureH {z : ℂ} (hz : z ∈ H) :
    MeasurableSet[hittingSigma] {A : Set ℂ | z ∈ rightSideOf (relClosureH A)} :=
  WangWu.measurableSet_mem_sideOf_relClosureH (I := Ioi 0)
    (Kw := fun N => Icc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1))
    (fun _ => isCompact_Icc) (fun N => nonempty_Icc.2 (WangWu.one_div_le_self_add_one N))
    (fun N x hx => show 0 < x by
      have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith [hx.1])
    (fun x hx => by
      obtain ⟨N, h1, h2⟩ := WangWu.exists_nat_window (show 0 < x from hx)
      exact ⟨N, h1, h2⟩) hz

/-- Membership of a point of `ℍ` in the left side of the relative closure is hitting-measurable. -/
theorem measurableSet_mem_leftSideOf_relClosureH {z : ℂ} (hz : z ∈ H) :
    MeasurableSet[hittingSigma] {A : Set ℂ | z ∈ leftSideOf (relClosureH A)} :=
  WangWu.measurableSet_mem_sideOf_relClosureH (I := Iio 0)
    (Kw := fun N => Icc (-((N : ℝ) + 1)) (-(1 / ((N : ℝ) + 1))))
    (fun _ => isCompact_Icc) (fun N => nonempty_Icc.2 (by linarith [WangWu.one_div_le_self_add_one N]))
    (fun N x hx => show x < 0 by
      have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith [hx.2])
    (fun x hx => by
      obtain ⟨N, h1, h2⟩ := WangWu.exists_nat_window (neg_pos.2 (show x < 0 from hx))
      exact ⟨N, by constructor <;> linarith⟩) hz

end Hitting

/-! ### Points between the walls -/

section Between

/-- A point **between the walls** `A` (right) and `B` (left), in the relative-closure form (measurable for the
hitting σ-algebra; the frozen form for proper arcs by `isBetweenPt_iff`). -/
def IsBetweenPt (A B : Set ℂ) (z : ℂ) : Prop :=
  z ∈ H ∧ z ∉ relClosureH (A ∪ B) ∧ z ∉ rightSideOf (relClosureH A) ∧ z ∉ leftSideOf (relClosureH B)

theorem relClosureH_union (A B : Set ℂ) : relClosureH (A ∪ B) = relClosureH A ∪ relClosureH B := by
  simp only [relClosureH, union_inter_distrib_right, closure_union, inter_union_distrib_left]

/-- For simple proper walls the relative-closure form is the frozen between condition of `betweenComponents`. -/
theorem isBetweenPt_iff {R L : ℝ≥0 → ℂ} (hR : IsSimpleProper R) (hL : IsSimpleProper L) {z : ℂ} :
    IsBetweenPt (range R) (range L) z ↔
      z ∈ H \ (range R ∪ range L) ∧ z ∉ rightSideOf (range R) ∧ z ∉ leftSideOf (range L) := by
  have hR' := hR.isProperArc
  have hL' := hL.isProperArc
  have h1 : relClosureH (range R) = range R ∩ H := by
    rw [← arcRange_realPath, hR'.relClosureH_arcRange]
  have h2 : relClosureH (range L) = range L ∩ H := by
    rw [← arcRange_realPath, hL'.relClosureH_arcRange]
  have h3 : rightSideOf (relClosureH (range R)) = rightSideOf (range R) := by
    rw [← arcRange_realPath, hR'.rightSideOf_relClosureH]
  have h4 : leftSideOf (relClosureH (range L)) = leftSideOf (range L) := by
    rw [← arcRange_realPath, hL'.leftSideOf_relClosureH]
  rw [IsBetweenPt, relClosureH_union, h3, h4, h1, h2]
  constructor
  · rintro ⟨hz, hzA, hzR, hzL⟩
    exact ⟨⟨hz, fun h => hzA (h.elim (fun h' => Or.inl ⟨h', hz⟩) fun h' => Or.inr ⟨h', hz⟩)⟩, hzR, hzL⟩
  · rintro ⟨⟨hz, hzA⟩, hzR, hzL⟩
    exact ⟨hz, fun h => hzA (h.elim (fun h' => Or.inl h'.1) fun h' => Or.inr h'.1), hzR, hzL⟩

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **Being between the random walls is a measurable event at a fixed point.** -/
theorem measurableSet_isBetweenPt {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hRm : ∀ t, Measurable[m] fun ω => R ω t)
    (hLm : ∀ t, Measurable[m] fun ω => L ω t) (z : ℂ) :
    MeasurableSet[m] {ω | IsBetweenPt (range (R ω)) (range (L ω)) z} := by
  by_cases hz : z ∈ H
  · have hA := measurable_range_hitting hRc hRm
    have hB := measurable_range_hitting hLc hLm
    have hAB := measurable_union_hitting hA hB
    have e : {ω | IsBetweenPt (range (R ω)) (range (L ω)) z} =
        ((fun ω => range (R ω) ∪ range (L ω)) ⁻¹' {S | z ∉ relClosureH S}) ∩
          ((fun ω => range (R ω)) ⁻¹' {S | z ∈ rightSideOf (relClosureH S)})ᶜ ∩
          ((fun ω => range (L ω)) ⁻¹' {S | z ∈ leftSideOf (relClosureH S)})ᶜ := by
      ext ω
      simp only [IsBetweenPt, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff, hz, true_and,
        and_assoc]
    rw [e]
    exact ((hAB (WangWu.measurableSet_notMem_relClosureH hz)).inter
      (hA (measurableSet_mem_rightSideOf_relClosureH hz)).compl).inter
      (hB (measurableSet_mem_leftSideOf_relClosureH hz)).compl
  · have e : {ω | IsBetweenPt (range (R ω)) (range (L ω)) z} = ∅ := by
      ext ω
      simp only [IsBetweenPt, mem_ofPred_eq, hz, false_and, mem_empty_iff_false]
    rw [e]
    exact @MeasurableSet.empty _ m

end Between

/-! ### The measurable pocket -/

section Select

/-- The default pocket (off the good event): the unit disc about `2i`. -/
def defaultPocket : Set ℂ := ball (2 * I) 1

theorem defaultPocket_subset_H : defaultPocket ⊆ H := fun z hz => by
  have h1 : |(z - 2 * I).im| < 1 := lt_of_le_of_lt (Complex.abs_im_le_norm _) (by rwa [← dist_eq_norm])
  have h2 : (z - 2 * I).im = z.im - 2 := by simp
  rw [h2, abs_lt] at h1
  show 0 < z.im
  linarith [h1.1]

theorem isConnected_defaultPocket : IsConnected defaultPocket := isConnected_ball one_pos

/-- The range of a simple proper curve is closed. -/
theorem IsSimpleProper.isClosed_range {η : ℝ≥0 → ℂ} (hη : IsSimpleProper η) : IsClosed (range η) := by
  rw [← arcRange_realPath]
  exact hη.isProperArc.isClosed_arcRange

/-- Every point of a component between two simple proper walls is between them. -/
theorem isBetweenPt_of_mem {R L : ℝ≥0 → ℂ} (hR : IsSimpleProper R) (hL : IsSimpleProper L) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) {z : ℂ} (hz : z ∈ C) : IsBetweenPt (range R) (range L) z := by
  have hC' : C ∈ betweenComponents (WangWu.arcRange (realPath R)) (WangWu.arcRange (realPath L)) := by
    rwa [arcRange_realPath, arcRange_realPath]
  have hsub := WangWu.subset_between_of_mem_betweenComponents hR.isProperArc hL.isProperArc hC' hz
  rw [arcRange_realPath, arcRange_realPath] at hsub
  have hzU : z ∈ H \ (range R ∪ range L) := by
    obtain ⟨z₀, -, -, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _ hz
  have hdR := hR.isProperArc.disjoint_leftSideOf_rightSideOf
  have hdL := hL.isProperArc.disjoint_leftSideOf_rightSideOf
  rw [arcRange_realPath] at hdR hdL
  refine (isBetweenPt_iff hR hL).2 ⟨hzU, fun h => Set.disjoint_left.1 hdR hsub.1 h,
    fun h => Set.disjoint_left.1 hdL h hsub.2⟩

/-- **Every component of the complement of two curves from `0` is simply connected** (the curves together with the
closed lower half-plane form a connected unbounded set; `LocalSets.isSimplyConnected_connectedComponentIn_compl`). -/
theorem isSimplyConnected_connectedComponentIn_range {R L : ℝ≥0 → ℂ} (hR : IsSimpleProper R)
    (hL : IsSimpleProper L) {y : ℂ} (hy : y ∈ H \ (range R ∪ range L)) :
    IsSimplyConnected (connectedComponentIn (H \ (range R ∪ range L)) y) := by
  have hS : IsOpen (H \ (range R ∪ range L)) :=
    QuantumZipper.isOpen_H.sdiff ((IsSimpleProper.isClosed_range hR).union (IsSimpleProper.isClosed_range hL))
  refine isSimplyConnected_connectedComponentIn_compl hS (fun z hz => ?_) hy
  have hlow : IsPreconnected {w : ℂ | w.im ≤ 0} := isPreconnected_lowerHalf
  have h0R : (0 : ℂ) ∈ range R := ⟨0, hR.2.2.1⟩
  have h0L : (0 : ℂ) ∈ range L := ⟨0, hL.2.2.1⟩
  have h0l : (0 : ℂ) ∈ {w : ℂ | w.im ≤ 0} := by simp
  have hRpc : IsPreconnected (range R) := isPreconnected_range hR.1
  have hLpc : IsPreconnected (range L) := isPreconnected_range hL.1
  have hpc : IsPreconnected (lowerUnion (range R ∪ range L)) := by
    have h1 := hRpc.union (0 : ℂ) h0R h0L hLpc
    exact h1.union (0 : ℂ) (Or.inl h0R) h0l hlow
  have heq : connectedComponentIn (lowerUnion (range R ∪ range L)) z = lowerUnion (range R ∪ range L) :=
    hpc.connectedComponentIn hz
  rw [heq]
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hm : ((-(|M| + 1) : ℝ) : ℂ) * I ∈ lowerUnion (range R ∪ range L) := Or.inr (by
    show ((((-(|M| + 1) : ℝ)) : ℂ) * I).im ≤ 0
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith [abs_nonneg M])
  have := hM _ hm
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [abs_nonneg M])]
    at this
  linarith [le_abs_self M]

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **A measurable choice of a pocket between the outer curves** (R2 of PROVE-LEMMA71I, the domain part). Let `R ω`,
`L ω` be continuous for every `ω` with `m`-measurable coordinates, and let `Good` be an `m`-measurable event on which
they are simple proper curves with a component between them. Then there are an `m`-measurable index `Np` (into a
dense sequence `e`) and a random open connected set `C ω ⊆ ℍ` with `m`-measurable closed-ball events and
`e (Np ω) ∈ C ω`, which is a component between the walls on `Good` (the one through the first rational
between-point) and the default disc off `Good`. -/
theorem exists_measurable_pocketSelection {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hRm : ∀ t, Measurable[m] fun ω => R ω t)
    (hLm : ∀ t, Measurable[m] fun ω => L ω t) {Good : Set Ω} (hGm : MeasurableSet[m] Good)
    (hG : ∀ ω ∈ Good, IsSimpleProper (R ω) ∧ IsSimpleProper (L ω) ∧
      (betweenComponents (range (R ω)) (range (L ω))).Nonempty)
    {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ (C : Ω → Set ℂ) (Np : Ω → ℕ), Measurable[m] Np ∧
      (∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H) ∧
      (∀ (c : ℂ) (r : ℝ), MeasurableSet[m] {ω | closedBall c r ⊆ C ω}) ∧ (∀ ω, e (Np ω) ∈ C ω) ∧
      (∀ ω ∈ Good, C ω ∈ betweenComponents (range (R ω)) (range (L ω))) ∧
      (∀ ω, ω ∉ Good → C ω = defaultPocket) := by
  classical
  let _ : MeasurableSpace Ω := m
  -- the first between index
  set B : ℕ → Set Ω := fun k => {ω | IsBetweenPt (range (R ω)) (range (L ω)) (e k)} with hBdef
  have hBm : ∀ k, MeasurableSet (B k) := fun k => measurableSet_isBetweenPt hRc hLc hRm hLm (e k)
  set p : Ω → ℕ → Prop := fun ω k => ω ∈ B k ∨ ∀ j, ω ∉ B j with hpdef
  have hp : ∀ ω, ∃ k, p ω k := fun ω => by
    by_cases h : ∃ j, ω ∈ B j
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, Or.inl hj⟩
    · push Not at h
      exact ⟨0, Or.inr h⟩
  have hpm : ∀ k, MeasurableSet {ω | p ω k} := fun k => by
    have e : {ω | p ω k} = B k ∪ ⋂ j, (B j)ᶜ := by
      ext ω
      simp only [hpdef, mem_ofPred_eq, mem_union, mem_iInter, mem_compl_iff]
    rw [e]
    exact (hBm k).union (MeasurableSet.iInter fun j => (hBm j).compl)
  set Nf : Ω → ℕ := fun ω => Nat.find (hp ω) with hNfdef
  have hNf : Measurable Nf := measurable_find hp hpm
  obtain ⟨k₀, hk₀⟩ := he.exists_mem_open isOpen_ball ⟨2 * I, mem_ball_self one_pos⟩
  set Np : Ω → ℕ := fun ω => if ω ∈ Good then Nf ω else k₀ with hNpdef
  have hNp : Measurable Np := Measurable.ite hGm hNf measurable_const
  -- on `Good` the selected point is between the walls
  have hGB : ∀ ω ∈ Good, ω ∈ B (Nf ω) := by
    intro ω hω
    obtain ⟨hR, hL, ⟨C₀, hC₀⟩⟩ := hG ω hω
    have hC₀o : IsOpen C₀ := by
      obtain ⟨z₀, -, -, -, rfl⟩ := hC₀
      exact (QuantumZipper.isOpen_H.sdiff ((IsSimpleProper.isClosed_range hR).union
        (IsSimpleProper.isClosed_range hL))).connectedComponentIn
    have hC₀ne : C₀.Nonempty := by
      obtain ⟨z₀, hz₀, -, -, rfl⟩ := hC₀
      exact ⟨z₀, mem_connectedComponentIn hz₀⟩
    obtain ⟨j, hj⟩ := he.exists_mem_open hC₀o hC₀ne
    have hjB : ω ∈ B j := isBetweenPt_of_mem hR hL hC₀ hj
    rcases Nat.find_spec (hp ω) with h | h
    · exact h
    · exact absurd hjB (h j)
  -- the random open domain
  set U : Ω → Set ℂ := fun ω => if ω ∈ Good then H \ (range (R ω) ∪ range (L ω)) else univ with hUdef
  have hUo : ∀ ω, IsOpen (U ω) := fun ω => by
    by_cases hω : ω ∈ Good
    · simp only [hUdef, hω, ↓reduceIte]
      exact QuantumZipper.isOpen_H.sdiff ((IsSimpleProper.isClosed_range (hG ω hω).1).union
        (IsSimpleProper.isClosed_range (hG ω hω).2.1))
    · simp only [hUdef, hω, ↓reduceIte]
      exact isOpen_univ
  have hUm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ U ω} := by
    intro c r
    have hcomp := Lemma71E.measurableSet_closedBall_subset_complement (η₁ := fun ω => realPath (R ω))
      (η₂ := fun ω => realPath (L ω)) (fun ω => ((hRc ω).comp continuous_real_toNNReal).continuousOn)
      (fun ω => ((hLc ω).comp continuous_real_toNNReal).continuousOn)
      (fun t _ => hRm t.toNNReal) (fun t _ => hLm t.toNNReal) c r
    have e : {ω | closedBall c r ⊆ U ω} =
        (Good ∩ {ω | closedBall c r ⊆ H \ (realPath (R ω) '' Ici 0 ∪ realPath (L ω) '' Ici 0)}) ∪ Goodᶜ := by
      ext ω
      by_cases hω : ω ∈ Good
      · simp only [hUdef, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, true_and, mem_compl_iff,
          not_true_eq_false, or_false]
        have h1 := arcRange_realPath (R ω)
        have h2 := arcRange_realPath (L ω)
        unfold WangWu.arcRange at h1 h2
        rw [h1, h2]
      · simp only [hUdef, hω, ↓reduceIte, mem_ofPred_eq, subset_univ, mem_union, mem_inter_iff, false_and,
          mem_compl_iff, not_false_eq_true, or_true]
    rw [e]
    exact (hGm.inter hcomp).union hGm.compl
  have hpU : ∀ ω, e (Np ω) ∈ U ω := fun ω => by
    by_cases hω : ω ∈ Good
    · simp only [hUdef, hNpdef, hω, ↓reduceIte]
      exact ((isBetweenPt_iff (hG ω hω).1 (hG ω hω).2.1).1 (hGB ω hω)).1
    · simp only [hUdef, hω, ↓reduceIte, mem_univ]
  -- the pocket
  set C : Ω → Set ℂ := fun ω => if ω ∈ Good then connectedComponentIn (U ω) (e (Np ω)) else defaultPocket
    with hCdef
  refine ⟨C, Np, hNp, fun ω => ?_, fun c r => ?_, fun ω => ?_, fun ω hω => ?_, fun ω hω => ?_⟩
  · by_cases hω : ω ∈ Good
    · simp only [hCdef, hω, ↓reduceIte]
      refine ⟨(hUo ω).connectedComponentIn, isConnected_connectedComponentIn_iff.2 (hpU ω), ?_, ?_⟩
      · have hpU' := hpU ω
        simp only [hUdef, hNpdef, hω, ↓reduceIte] at hpU' ⊢
        exact isSimplyConnected_connectedComponentIn_range (hG ω hω).1 (hG ω hω).2.1 hpU'
      · refine (connectedComponentIn_subset _ _).trans ?_
        simp only [hUdef, hω, ↓reduceIte]
        exact sdiff_subset
    · simp only [hCdef, hω, ↓reduceIte]
      exact ⟨isOpen_ball, isConnected_defaultPocket, isSimplyConnected_ball _ one_pos, defaultPocket_subset_H⟩
  · have hc := Lemma71E.measurableSet_closedBall_subset_component hUo hUm hNp hpU c r
    have e : {ω | closedBall c r ⊆ C ω} =
        (Good ∩ {ω | closedBall c r ⊆ connectedComponentIn (U ω) (e (Np ω))}) ∪
          (Goodᶜ ∩ {_ω | closedBall c r ⊆ defaultPocket}) := by
      ext ω
      by_cases hω : ω ∈ Good <;> simp [hCdef, hω]
    rw [e]
    exact (hGm.inter hc).union (hGm.compl.inter (MeasurableSet.const _))
  · by_cases hω : ω ∈ Good
    · simp only [hCdef, hω, ↓reduceIte]
      exact mem_connectedComponentIn (hpU ω)
    · simp only [hCdef, hNpdef, hω, ↓reduceIte]
      exact hk₀
  · have hb := (isBetweenPt_iff (hG ω hω).1 (hG ω hω).2.1).1 (hGB ω hω)
    simp only [hCdef, hUdef, hNpdef, hω, ↓reduceIte]
    exact ⟨e (Nf ω), hb.1, hb.2.1, hb.2.2, rfl⟩
  · simp only [hCdef, hω, ↓reduceIte]

end Select

/-! ### The good event has full measure on the three-curve space -/

section Ae

open MeasureTheory

universe u

variable {κ θ₁ θ₂ a b : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}

/-- **On the three-curve space a pocket exists almost surely.** Under the hypotheses of `Lemma71I.ae_isOrderedArcs`
(Lemma 6.13's input discharged by `Lemma613.lemma613ContactStatement_of_prop55`), almost surely the outer curves `α`
(right wall, angle `θ₁`) and `β` (left wall, angle `θ₂`) are simple proper curves, the three curves are ordered, and
there is a component between the outer curves (the walls differ: `α` has no arc on `β`, Lemma 6.13; a chamber exists,
`WangWu.nonempty_betweenComponents`). -/
theorem ae_nonempty_betweenComponents (href : Lemma71H.Cond44ReferenceStatement.{u})
    (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (ha : sleLambda κ - π * QuantumZipper.chiC κ + θ₂ * QuantumZipper.chiC κ ≤ a)
    (hb : sleLambda κ - θ₁ * QuantumZipper.chiC κ ≤ b)
    (hh : IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ))
    (hβf : IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h β ζβ) (hαf : IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h α ζα)
    (hγf : IsFlowLine κ (prop74Data a b) {0} 0 0 P h γ ζγ)
    (hord : ∀ᵐ ω ∂P, range (β ω) ⊆ closedLeftSide (γ ω) ∧ range (γ ω) ⊆ closedLeftSide (α ω)) :
    ∀ᵐ ω ∂P, IsSimpleProper (α ω) ∧ IsSimpleProper (β ω) ∧
      (betweenComponents (range (α ω)) (range (β ω))).Nonempty := by
  have hMD := Lemma613.lemma613ContactStatement_of_prop55 href h55
  have hαβ := hMD κ hκ hκ4 a b θ₁ θ₂ (hθ₁.trans hθ₂) hb ha P h hh α β ζα ζβ hαf hβf
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπ : 0 ≤ π * QuantumZipper.chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  have hb41 : sleLambda κ - π * QuantumZipper.chiC κ - θ₁ * QuantumZipper.chiC κ ≤ b := by linarith
  have hpc := isPiecewiseConstant_prop74Data a b
  obtain ⟨hLα, hRα⟩ := Lemma71G.prop74Data_remark41 hκ hκ4 le_rfl (hθ₁.trans hθ₂).le ha hb41
  obtain ⟨hLβ, hRβ⟩ := Lemma71G.prop74Data_remark41 hκ hκ4 (hθ₁.trans hθ₂).le le_rfl ha hb41
  filter_upwards [ae_isOrderedArcs hMD hκ hκ4 hθ₁ hθ₂ ha hb hh hβf hαf hγf hord,
    IsFlowLine.ae_isSimpleProper_angle hκ hκ4.le hpc hLα hRα hαf,
    IsFlowLine.ae_isSimpleProper_angle hκ hκ4.le hpc hLβ hRβ hβf, hαβ] with ω hω hαω hβω hαβω
  obtain ⟨hβs, hαs, -, hord3, -, -⟩ := hω
  have hnc := (hαβω hαω.1 hβω.1).1
  obtain ⟨t, -, -, ht⟩ := hnc 1 2 one_pos one_lt_two
  have hne : ¬ WangWu.arcRange (realPath (α ω)) ⊆ WangWu.arcRange (realPath (β ω)) := by
    rw [arcRange_realPath, arcRange_realPath]
    exact fun hsub => ht (hsub ⟨t, rfl⟩)
  have := WangWu.nonempty_betweenComponents hαs.isProperArc hβs.isProperArc hord3.right_left hne
  rw [arcRange_realPath, arcRange_realPath] at this
  exact ⟨hαs, hβs, this⟩

end Ae

end InteractingSLE.Sec7.Lemma71Pin
