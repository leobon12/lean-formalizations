/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22ChartESpan
import InteractingSLE.Spec.Sec4.Prob41Lemmas
import InteractingSLE.Spec.Sec4.ZeroMarks
import InteractingSLE.Spec.Sec4.ZeroMarksAvoid
import InteractingSLE.Spec.Supplement.GW0
import InteractingSLE.Spec.Supplement.GB7aB
import InteractingSLE.Spec.Supplement.GW1Base

/-!
# Aux. lemma 22, chart `E`, step 2: the first contact with a left span, for a flow line from `0`

Packet PROVE-SEC5-M (specification §4.1, Aux. lemma 22 and its proof, pp. 113–115). For the flow line from `0` (angle
`0`) of a field with piecewise-constant boundary data `b` on `∂ℍ` whose seed weights vanish (`b(0⁻) = −λ`,
`b(0⁺) = λ`), and an interval `(−C, −A)` of the negative axis carrying one height `a + πχ` with `|a| < λ`,
**`IsFlowLine.ae_exists_hit_left`** shows: if `b ≤ −λ + πχ` on `(−A, 0)`, `b ≥ λ + πχ` on `(−∞, −C)` and
`b ≥ λ − πχ` on `(0, ∞)` (off the jumps), then almost surely the flow line reaches a point of `(−C, −A)` at a finite
time `t` (at most its lifetime) and never visits `ℝ \ {0}` before `t`.

Proof: drop the two seed marks (weight `0`, `IsIntegratedSLEEvolution.compEmb`), reflect
(`IsIntegratedSLEEvolution.reflect`), and apply the span form of PROVE-SEC5-L's chordal theorem
(`ae_exists_hit_of_span`). `−A` and `−C` are genuine jumps of `b`, hence consecutive marks of nonzero weight, and
the cumulative weight at each mark is the conversion of the data just beyond it (`exists_sum_flowLineRhoL_eq`,
`exists_sum_flowLineRhoR_eq`, from `Sec4.forceBoundaryData_flowLine`).

Helpers: `exists_left_le_prefix_eq` (a point just left of a mark with the same prefix), `exists_leftLim_eq`,
`exists_rightLim_eq` (one-sided limits are values just beside the point), `exists_flowLineXL_eq` (a genuine jump
`z < 0` is a left mark of nonzero weight).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE

namespace Sec5

namespace Aux22ChartE

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open QuantumZipper (chiC)

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-- A point `y ∈ (lo, p)` off a finite set with the same left prefix: the marks strictly right of `y` are those
at or right of `p`. -/
theorem exists_left_le_prefix_eq {N : ℕ} (x : Fin N → ℝ) (E : Finset ℝ) {lo p : ℝ} (h : lo < p) :
    ∃ y, lo < y ∧ y < p ∧ y ∉ E ∧
      univ.filter (fun i => y < x i) = univ.filter (fun i => p ≤ x i) := by
  set M : Finset ℝ := insert lo ((univ.filter (fun i => x i < p)).image x) with hM
  have hMne : M.Nonempty := insert_nonempty _ _
  have hmp : M.max' hMne < p := by
    rcases Finset.mem_insert.1 (M.max'_mem hMne) with h' | h'
    · rw [h']; exact h
    · obtain ⟨i, hi, hix⟩ := Finset.mem_image.1 h'
      rw [← hix]; exact (Finset.mem_filter.1 hi).2
  have hlom : lo ≤ M.max' hMne := M.le_max' lo (mem_insert_self _ _)
  obtain ⟨y, h1, h2, hE⟩ := Sec4.exists_mem_Ioo_not_mem E hmp
  refine ⟨y, lt_of_le_of_lt hlom h1, h2, hE, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra hcon
    have : x i ≤ M.max' hMne := M.le_max' _ (mem_insert_of_mem (Finset.mem_image.2
      ⟨i, Finset.mem_filter.2 ⟨mem_univ _, not_le.1 hcon⟩, rfl⟩))
    linarith
  · intro hi; linarith

/-- The right limit of piecewise-constant data at `z` is its value at some point of `(z, hi)` off the jumps. -/
theorem exists_rightLim_eq (hb : IsPiecewiseConstantBoundaryData b J) {z hi : ℝ} (hz : z < hi) :
    ∃ t, z < t ∧ t < hi ∧ t ∉ J ∧ rightLim b z = b t := by
  set M : Finset ℝ := insert hi (J.filter (z < ·)) with hM
  have hMne : M.Nonempty := insert_nonempty _ _
  have hzm : z < M.min' hMne := by
    rcases Finset.mem_insert.1 (M.min'_mem hMne) with h' | h'
    · rw [h']; exact hz
    · exact (Finset.mem_filter.1 h').2
  have hmhi : M.min' hMne ≤ hi := M.min'_le hi (mem_insert_self _ _)
  have hnoJ : ∀ w ∈ J, w ∉ Set.Ioo z (M.min' hMne) := fun w hwJ hw =>
    absurd (M.min'_le w (mem_insert_of_mem (Finset.mem_filter.2 ⟨hwJ, hw.1⟩))) (not_le.2 hw.2)
  set t := (z + M.min' hMne) / 2 with ht
  have htI : t ∈ Set.Ioo z (M.min' hMne) := ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
  refine ⟨t, htI.1, htI.2.trans_le hmhi, fun h' => hnoJ t h' htI, ?_⟩
  exact Sec4.rightLim_eq_of_forall hzm fun s hs => Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ htI hs

/-- The left limit of piecewise-constant data at `z` is its value at some point of `(lo, z)` off the jumps. -/
theorem exists_leftLim_eq (hb : IsPiecewiseConstantBoundaryData b J) {z lo : ℝ} (hz : lo < z) :
    ∃ t, lo < t ∧ t < z ∧ t ∉ J ∧ leftLim b z = b t := by
  set M : Finset ℝ := insert lo (J.filter (· < z)) with hM
  have hMne : M.Nonempty := insert_nonempty _ _
  have hmz : M.max' hMne < z := by
    rcases Finset.mem_insert.1 (M.max'_mem hMne) with h' | h'
    · rw [h']; exact hz
    · exact (Finset.mem_filter.1 h').2
  have hlom : lo ≤ M.max' hMne := M.le_max' lo (mem_insert_self _ _)
  have hnoJ : ∀ w ∈ J, w ∉ Set.Ioo (M.max' hMne) z := fun w hwJ hw =>
    absurd (M.le_max' w (mem_insert_of_mem (Finset.mem_filter.2 ⟨hwJ, hw.2⟩))) (not_le.2 hw.1)
  set t := (M.max' hMne + z) / 2 with ht
  have htI : t ∈ Set.Ioo (M.max' hMne) z := ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
  refine ⟨t, lt_of_le_of_lt hlom htI.1, htI.2, fun h' => hnoJ t h' htI, ?_⟩
  exact Sec4.leftLim_eq_of_forall hmz fun s hs => Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ htI hs

variable {κ : ℝ}

/-- **The left cumulative weight at a position `p ≤ 0`** of the flow-line word from `0` (angle `0`) is the
conversion `−b(y)/λ − 1` of the data at some `y ∈ (lo, p)` off the jumps. -/
theorem exists_sum_flowLineRhoL_eq (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) {lo p : ℝ}
    (hlo : lo < p) (hp : p ≤ 0) :
    ∃ y, lo < y ∧ y < p ∧ y ∉ J ∧
      ∑ i ∈ univ.filter (fun i => p ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 0 i =
        Sec4.cumWeightLeft κ (b y) := by
  obtain ⟨y, h1, h2, hE, hS⟩ := exists_left_le_prefix_eq (flowLineXL b J 0) (insert 0 J) hlo
  have hy0 : y < 0 := h2.trans_le hp
  have hyJ : y ∉ J := fun h => hE (mem_insert_of_mem h)
  refine ⟨y, h1, h2, hyJ, ?_⟩
  rw [← hS, ← Sec4.cumWeightLeft_forceBoundaryData hκ _ (flowLineRhoR κ b J 0 0) _ (flowLineXR b J 0) hy0,
    Sec4.forceBoundaryData_flowLine hκ hb hy0.ne hyJ]

/-- **The right cumulative weight at a position `q ≥ 0`** of the flow-line word from `0` (angle `0`) is the
conversion `b(y)/λ − 1` of the data at some `y > q` off the jumps. -/
theorem exists_sum_flowLineRhoR_eq (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) {q : ℝ}
    (hq : 0 ≤ q) :
    ∃ y, q < y ∧ y ∉ J ∧
      ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ q), flowLineRhoR κ b J 0 0 i =
        Sec4.cumWeightRight κ (b y) := by
  obtain ⟨y, h1, hE, hS⟩ := Sec4.exists_right_prefix_eq (flowLineXR b J 0) (insert 0 J) q
  have hy0 : 0 < y := hq.trans_lt h1
  have hyJ : y ∉ J := fun h => hE (mem_insert_of_mem h)
  refine ⟨y, h1, hyJ, ?_⟩
  rw [← hS, ← Sec4.cumWeightRight_forceBoundaryData hκ (flowLineRhoL κ b J 0 0) _ (flowLineXL b J 0) _ hy0.le,
    Sec4.forceBoundaryData_flowLine hκ hb hy0.ne' hyJ]

/-- A genuine jump `z < 0` of the data is a left mark of the flow-line word from `0`, with nonzero weight. -/
theorem exists_flowLineXL_eq {z : ℝ} (hz : z ∈ jumpSet b J) (hz0 : z < 0) (hκ : 0 < κ) :
    ∃ i, flowLineXL b J 0 i = z ∧ flowLineRhoL κ b J 0 0 i ≠ 0 := by
  set S := (jumpSet b J).filter (· < 0) with hS
  have hzS : z ∈ S := Finset.mem_filter.2 ⟨hz, hz0⟩
  obtain ⟨k, hk⟩ : ∃ k, S.orderEmbOfFin rfl k = z := by
    have : z ∈ Set.range (S.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hzS
    exact this
  have hgen : leftLim b z ≠ rightLim b z := (Finset.mem_filter.1 hz).2
  refine ⟨(Fin.succ (Fin.rev k) : Fin (S.card + 1)), ?_, ?_⟩
  · show (Fin.cons (0 : ℝ) (fun i : Fin S.card => S.orderEmbOfFin rfl (Fin.rev i) - 0) :
      Fin (S.card + 1) → ℝ) (Fin.succ (Fin.rev k)) = z
    rw [Fin.cons_succ, Fin.rev_rev, sub_zero]
    exact hk
  · show (Fin.cons (-(leftLim b 0 + 0 * chiC κ) / sleLambda κ - 1)
      (fun i : Fin S.card => (rightLim b (S.orderEmbOfFin rfl (Fin.rev i)) -
        leftLim b (S.orderEmbOfFin rfl (Fin.rev i))) / sleLambda κ) :
      Fin (S.card + 1) → ℝ) (Fin.succ (Fin.rev k)) ≠ 0
    rw [Fin.cons_succ, Fin.rev_rev, hk]
    exact div_ne_zero (sub_ne_zero.2 hgen.symm) (Sec4.sleLambda_pos hκ).ne'



/-- **Aux. lemma 22 for a flow line from `0`, one height on a left span, zero seed weights** (`0 < κ ≤ 4`):
almost surely the flow line reaches a point of `(−C, −A)` at a finite time `t ≤ ζ` and never visits `ℝ \ {0}`
before `t`. -/
theorem IsFlowLine.ae_exists_hit_left (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hseedL : leftLim b 0 = -sleLambda κ) (hseedR : rightLim b 0 = sleLambda κ) {A C a : ℝ} (hA : 0 < A)
    (hAC : A < C) (ha : -sleLambda κ < a) (ha' : a < sleLambda κ)
    (h1 : ∀ y, -A < y → y < 0 → y ∉ J → b y ≤ -sleLambda κ + π * chiC κ)
    (h2 : ∀ y, -C < y → y < -A → y ∉ J → b y = a + π * chiC κ)
    (h3 : ∀ y, y < -C → y ∉ J → sleLambda κ + π * chiC κ ≤ b y)
    (h4 : ∀ y, 0 < y → y ∉ J → sleLambda κ - π * chiC κ ≤ b y)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b J 0 0 P h η ζ) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η ω s ≠ z) ∧
      ∃ x : ℝ, -C < x ∧ x < -A ∧ η ω t = x := by
  obtain ⟨𝓕, W, VL, VR, B, hE, htr⟩ := Sec4.IsFlowLine.exists_evolution hfl
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlam := Sec4.sleLambda_pos hκ
  set xL := flowLineXL b J 0 with hxLdef
  set xR := flowLineXR b J 0 with hxRdef
  set ρL := flowLineRhoL κ b J 0 0 with hρLdef
  set ρR := flowLineRhoR κ b J 0 0 with hρRdef
  -- the seed weights vanish
  have hρL0 : ρL ⟨0, by unfold flowLineNL; omega⟩ = 0 := by
    show -(leftLim b 0 + 0 * chiC κ) / sleLambda κ - 1 = 0
    rw [hseedL, zero_mul, add_zero, neg_neg, div_self hlam.ne', sub_self]
  have hρR0 : ρR ⟨0, by unfold flowLineNR; omega⟩ = 0 := by
    show (rightLim b 0 + 0 * chiC κ) / sleLambda κ - 1 = 0
    rw [hseedR, zero_mul, add_zero, div_self hlam.ne', sub_self]
  set eL := Sec4.nonzeroEmb ρL with heL
  set eR := Sec4.nonzeroEmb ρR with heR
  have hzL : ∀ i, i ∉ Set.range eL → ρL i = 0 := fun _ hi => Sec4.eq_zero_of_notMem_range_nonzeroEmb hi
  have hzR : ∀ i, i ∉ Set.range eR → ρR i = 0 := fun _ hi => Sec4.eq_zero_of_notMem_range_nonzeroEmb hi
  have hxLd : ∀ j, xL (eL j) < 0 := by
    intro j
    have hne : eL j ≠ ⟨0, by unfold flowLineNL; omega⟩ := fun he =>
      Sec4.nonzero_nonzeroEmb ρL j (by rw [← heL, he]; exact hρL0)
    have hpos : (⟨0, by unfold flowLineNL; omega⟩ : Fin (flowLineNL b J 0)) < eL j := by
      rw [Fin.lt_def]; have := Fin.val_ne_of_ne hne; simp at this ⊢; omega
    exact Theorem14.GW0.flowLineXL_lt b J 0 hpos
  have hxRd : ∀ j, 0 < xR (eR j) := by
    intro j
    have hne : eR j ≠ ⟨0, by unfold flowLineNR; omega⟩ := fun he =>
      Sec4.nonzero_nonzeroEmb ρR j (by rw [← heR, he]; exact hρR0)
    have hpos : (⟨0, by unfold flowLineNR; omega⟩ : Fin (flowLineNR b J 0)) < eR j := by
      rw [Fin.lt_def]; have := Fin.val_ne_of_ne hne; simp at this ⊢; omega
    exact Theorem14.GW0.flowLineXR_lt b J 0 hpos
  -- `−A` and `−C` are genuine jumps, hence marks of nonzero weight
  have hAj : -A ∈ jumpSet b J := by
    have hl : leftLim b (-A) = a + π * chiC κ :=
      Sec4.leftLim_eq_of_forall_notMem J (by linarith : -C < -A) fun t ht htJ => h2 t ht.1 ht.2 htJ
    obtain ⟨t, ht1, ht2, htJ, hr⟩ := exists_rightLim_eq hb (by linarith : -A < 0)
    have hr' : rightLim b (-A) ≤ -sleLambda κ + π * chiC κ := hr ▸ h1 t ht1 ht2 htJ
    have hne : leftLim b (-A) ≠ rightLim b (-A) := by
      rw [hl]; intro he; rw [← he] at hr'; linarith
    refine Finset.mem_filter.2 ⟨?_, hne⟩
    by_contra hJ
    exact hne (Theorem14.GW1.leftLim_eq_rightLim_of_notMem hb hJ)
  have hCj : -C ∈ jumpSet b J := by
    have hr : rightLim b (-C) = a + π * chiC κ :=
      Sec4.rightLim_eq_of_forall_notMem J (by linarith : -C < -A) fun t ht htJ => h2 t ht.1 ht.2 htJ
    obtain ⟨t, ht1, ht2, htJ, hl⟩ := exists_leftLim_eq hb (by linarith : -C - 1 < -C)
    have hl' : sleLambda κ + π * chiC κ ≤ leftLim b (-C) := hl ▸ h3 t ht2 htJ
    have hne : leftLim b (-C) ≠ rightLim b (-C) := by
      rw [hr]; intro he; rw [he] at hl'; linarith
    refine Finset.mem_filter.2 ⟨?_, hne⟩
    by_contra hJ
    exact hne (Theorem14.GW1.leftLim_eq_rightLim_of_notMem hb hJ)
  obtain ⟨iA, hiA, hiA0⟩ := exists_flowLineXL_eq (κ := κ) hAj (by linarith) hκ
  obtain ⟨iC, hiC, hiC0⟩ := exists_flowLineXL_eq (κ := κ) hCj (by linarith) hκ
  obtain ⟨ja, hja⟩ := Sec4.exists_nonzeroEmb_eq hiA0
  obtain ⟨jc, hjc⟩ := Sec4.exists_nonzeroEmb_eq hiC0
  -- the reflected sub-word of nonzero weights
  have hEr := (hE.compEmb eL eR hzL hzR).reflect
  have hsL : StrictAnti (fun j => xL (eL j)) := fun i i' hii =>
    Theorem14.GW0.flowLineXL_lt b J 0 (eL.strictMono hii)
  have hsR : StrictMono (fun j => xR (eR j)) := fun i i' hii =>
    Theorem14.GW0.flowLineXR_lt b J 0 (eR.strictMono hii)
  have hD : LP.IsDistinctForceWord (-fun j => xR (eR j)) (-fun j => xL (eL j)) :=
    LP.IsDistinctForceWord.reflect ⟨⟨hsL.antitone, fun j => (hxLd j).le, hsR.monotone, fun j => (hxRd j).le⟩,
      hsL, hsR⟩
  have hxA : (-fun j => xL (eL j)) ja = A := by
    simp only [Pi.neg_apply]; rw [hja, hxLdef, hiA, neg_neg]
  have hxC : (-fun j => xL (eL j)) jc = C := by
    simp only [Pi.neg_apply]; rw [hjc, hxLdef, hiC, neg_neg]
  have hgap : ∀ j, (-fun j => xL (eL j)) j ∉
      Set.Ioo ((-fun j => xL (eL j)) ja) ((-fun j => xL (eL j)) jc) := by
    intro j hj
    rw [hxA, hxC] at hj
    simp only [Pi.neg_apply] at hj
    rcases Supp8.flowLineXL_cases 0 (eL j) with h0 | ⟨z, hzJ, hz0, hz⟩
    · rw [hxLdef, h0] at hj; linarith [hj.1]
    · rw [hxLdef, hz, sub_zero] at hj
      have hl : leftLim b z = a + π * chiC κ :=
        Sec4.leftLim_eq_of_forall_notMem J (by linarith [hj.2] : -C < z) fun t ht htJ =>
          h2 t ht.1 (ht.2.trans (by linarith [hj.1])) htJ
      have hr : rightLim b z = a + π * chiC κ :=
        Sec4.rightLim_eq_of_forall_notMem J (by linarith [hj.1] : z < -A) fun t ht htJ =>
          h2 t (by linarith [ht.1, hj.2]) ht.2 htJ
      exact (Finset.mem_filter.1 hzJ).2 (hl.trans hr.symm)
  -- cumulative weights of the reflected word
  have hsumL : ∀ i, ∑ j ∈ univ.filter (fun j => (-fun j => xL (eL j)) j ≤ (-fun j => xL (eL j)) i),
      ρL (eL j) = ∑ i' ∈ univ.filter (fun i' => xL (eL i) ≤ xL i'), ρL i' := by
    intro i
    rw [← Sec4.sum_filter_comp_embedding eL eL.injective ρL hzL]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j; simp
  have hsumR : ∀ i, ∑ j ∈ univ.filter (fun j => (-fun j => xR (eR j)) i ≤ (-fun j => xR (eR j)) j),
      ρR (eR j) = ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR (eR i)), ρR i' := by
    intro i
    rw [← Sec4.sum_filter_comp_embedding eR eR.injective ρR hzR]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j; simp
  have hL : ∀ i, κ / 2 - 2 ≤ ∑ j ∈ univ.filter (fun j => (-fun j => xR (eR j)) i ≤ (-fun j => xR (eR j)) j),
      ρR (eR j) := by
    intro i
    rw [hsumR]
    obtain ⟨y, hy, hyJ, hS⟩ := exists_sum_flowLineRhoR_eq (κ := κ) hκ hb (hxRd i).le
    rw [hS]
    exact (Sec4.le_cumWeightRight_iff hκ).2 (h4 y ((hxRd i).trans hy) hyJ)
  have hR1 : ∀ i, (-fun j => xL (eL j)) i < (-fun j => xL (eL j)) ja →
      κ / 2 - 2 ≤ ∑ j ∈ univ.filter (fun j => (-fun j => xL (eL j)) j ≤ (-fun j => xL (eL j)) i),
        ρL (eL j) := by
    intro i hi
    rw [hxA] at hi
    simp only [Pi.neg_apply] at hi
    rw [hsumL]
    obtain ⟨y, hy1, hy2, hyJ, hS⟩ := exists_sum_flowLineRhoL_eq (κ := κ) hκ hb (lo := -A) (by linarith)
      (hxLd i).le
    rw [hS]
    exact (Sec4.le_cumWeightLeft_iff hκ).2 (h1 y hy1 (hy2.trans (hxLd i)) hyJ)
  have hR2 : Sec4.cumWeightLeft κ (a + π * chiC κ) =
      ∑ j ∈ univ.filter (fun j => (-fun j => xL (eL j)) j ≤ (-fun j => xL (eL j)) ja), ρL (eL j) := by
    rw [hsumL]
    have hp : xL (eL ja) = -A := by rw [hja, hxLdef, hiA]
    obtain ⟨y, hy1, hy2, hyJ, hS⟩ := exists_sum_flowLineRhoL_eq (κ := κ) hκ hb (lo := -C)
      (p := xL (eL ja)) (by rw [hp]; linarith) (by rw [hp]; linarith)
    rw [hS, h2 y hy1 (hp ▸ hy2) hyJ]
  have hRa : Sec4.cumWeightLeft κ (a + π * chiC κ) = κ / 2 - 3 - a / sleLambda κ := by
    rw [Sec4.cumWeightLeft_add_pi_mul_chiC hκ]; rfl
  have had : a / sleLambda κ < 1 := (div_lt_one hlam).2 ha'
  have had' : -1 < a / sleLambda κ := by
    rw [lt_div_iff₀ hlam]; linarith
  have hR3 : ∀ i, (-fun j => xL (eL j)) jc ≤ (-fun j => xL (eL j)) i →
      ∑ j ∈ univ.filter (fun j => (-fun j => xL (eL j)) j ≤ (-fun j => xL (eL j)) i),
        ρL (eL j) ≤ κ / 2 - 4 := by
    intro i hi
    rw [hxC] at hi
    simp only [Pi.neg_apply] at hi
    rw [hsumL]
    obtain ⟨y, hy1, hy2, hyJ, hS⟩ := exists_sum_flowLineRhoL_eq (κ := κ) hκ hb (lo := xL (eL i) - 1)
      (by linarith) (hxLd i).le
    rw [hS]
    have hby := h3 y (by linarith) hyJ
    have e : b y = (b y - π * chiC κ) + π * chiC κ := by ring
    rw [e, Sec4.cumWeightLeft_add_pi_mul_chiC hκ]
    show κ / 2 - 3 - (b y - π * chiC κ) / sleLambda κ ≤ κ / 2 - 4
    have : 1 ≤ (b y - π * chiC κ) / sleLambda κ := by
      rw [le_div_iff₀ hlam]; linarith
    linarith
  have hac : (-fun j => xL (eL j)) ja < (-fun j => xL (eL j)) jc := by rw [hxA, hxC]; exact hAC
  have key := ae_exists_hit_of_span hκ hκ4 hEr hD (fun i => by simp only [Pi.neg_apply]; linarith [hxRd i])
    (fun i => by simp only [Pi.neg_apply]; linarith [hxLd i]) hac hgap hL hR1
    (by rw [← hR2, hRa]; linarith) (by rw [← hR2, hRa]; linarith) hR3
  filter_upwards [key, htr] with ω hω hη
  have hη' : IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) (fun t => LP.reflectC (η ω t)) :=
    LP.isGeneratingTrace_reflect hη
  obtain ⟨t, htζ, hav, x, hx1, hx2, hxt⟩ := hω _ hη'
  rw [hxA] at hx1
  rw [hxC] at hx2
  refine ⟨t, htζ, fun s hs z hz he => hav s hs (-z) (neg_ne_zero.2 hz) ?_, -x, by linarith, by linarith, ?_⟩
  · rw [he]; simp [LP.reflectC]
  · have := congrArg LP.reflectC hxt
    rw [LP.reflectC_reflectC] at this
    rw [this]; simp [LP.reflectC]

/-- **The same with seed marks, from the named chordal input** (`SeedSpanHitStatement`): no condition on the seed
weights beyond the value conditions (`h1`, `h4` make both at least `κ/2 − 2`). The full flow-line word is reflected
(no mark is dropped). -/
theorem IsFlowLine.ae_exists_hit_left_of_seedSpanHit (hseed : SeedSpanHitStatement.{u} κ) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J) {A C a : ℝ} (hA : 0 < A)
    (hAC : A < C) (ha : -sleLambda κ < a) (ha' : a < sleLambda κ)
    (h1 : ∀ y, -A < y → y < 0 → y ∉ J → b y ≤ -sleLambda κ + π * chiC κ)
    (h2 : ∀ y, -C < y → y < -A → y ∉ J → b y = a + π * chiC κ)
    (h3 : ∀ y, y < -C → y ∉ J → sleLambda κ + π * chiC κ ≤ b y)
    (h4 : ∀ y, 0 < y → y ∉ J → sleLambda κ - π * chiC κ ≤ b y)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b J 0 0 P h η ζ) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η ω s ≠ z) ∧
      ∃ x : ℝ, -C < x ∧ x < -A ∧ η ω t = x := by
  obtain ⟨𝓕, W, VL, VR, B, hE, htr⟩ := Sec4.IsFlowLine.exists_evolution hfl
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hlam := Sec4.sleLambda_pos hκ
  set xL := flowLineXL b J 0 with hxLdef
  set xR := flowLineXR b J 0 with hxRdef
  set ρL := flowLineRhoL κ b J 0 0 with hρLdef
  set ρR := flowLineRhoR κ b J 0 0 with hρRdef
  -- `−A` and `−C` are genuine jumps, hence marks
  have hAj : -A ∈ jumpSet b J := by
    have hl : leftLim b (-A) = a + π * chiC κ :=
      Sec4.leftLim_eq_of_forall_notMem J (by linarith : -C < -A) fun t ht htJ => h2 t ht.1 ht.2 htJ
    obtain ⟨t, ht1, ht2, htJ, hr⟩ := exists_rightLim_eq hb (by linarith : -A < 0)
    have hr' : rightLim b (-A) ≤ -sleLambda κ + π * chiC κ := hr ▸ h1 t ht1 ht2 htJ
    have hne : leftLim b (-A) ≠ rightLim b (-A) := by
      rw [hl]; intro he; rw [← he] at hr'; linarith
    refine Finset.mem_filter.2 ⟨?_, hne⟩
    by_contra hJ
    exact hne (Theorem14.GW1.leftLim_eq_rightLim_of_notMem hb hJ)
  have hCj : -C ∈ jumpSet b J := by
    have hr : rightLim b (-C) = a + π * chiC κ :=
      Sec4.rightLim_eq_of_forall_notMem J (by linarith : -C < -A) fun t ht htJ => h2 t ht.1 ht.2 htJ
    obtain ⟨t, ht1, ht2, htJ, hl⟩ := exists_leftLim_eq hb (by linarith : -C - 1 < -C)
    have hl' : sleLambda κ + π * chiC κ ≤ leftLim b (-C) := hl ▸ h3 t ht2 htJ
    have hne : leftLim b (-C) ≠ rightLim b (-C) := by
      rw [hr]; intro he; rw [he] at hl'; linarith
    refine Finset.mem_filter.2 ⟨?_, hne⟩
    by_contra hJ
    exact hne (Theorem14.GW1.leftLim_eq_rightLim_of_notMem hb hJ)
  obtain ⟨iA, hiA, -⟩ := exists_flowLineXL_eq (κ := κ) hAj (by linarith) hκ
  obtain ⟨iC, hiC, -⟩ := exists_flowLineXL_eq (κ := κ) hCj (by linarith) hκ
  -- the reflected word
  have hEr := hE.reflect
  have hsL : StrictAnti xL := fun i i' hii => Theorem14.GW0.flowLineXL_lt b J 0 hii
  have hsR : StrictMono xR := fun i i' hii => Theorem14.GW0.flowLineXR_lt b J 0 hii
  have hD : LP.IsDistinctForceWord (-xR) (-xL) :=
    LP.IsDistinctForceWord.reflect ⟨Theorem15.isOrderedForceWord_flowLine b J 0, hsL, hsR⟩
  have hxA : (-xL) iA = A := by simp only [Pi.neg_apply]; rw [hxLdef, hiA, neg_neg]
  have hxC : (-xL) iC = C := by simp only [Pi.neg_apply]; rw [hxLdef, hiC, neg_neg]
  have hgap : ∀ j, (-xL) j ∉ Set.Ioo ((-xL) iA) ((-xL) iC) := by
    intro j hj
    rw [hxA, hxC] at hj
    simp only [Pi.neg_apply] at hj
    rcases Supp8.flowLineXL_cases 0 j with h0 | ⟨z, hzJ, hz0, hz⟩
    · rw [hxLdef, h0] at hj; linarith [hj.1]
    · rw [hxLdef, hz, sub_zero] at hj
      have hl : leftLim b z = a + π * chiC κ :=
        Sec4.leftLim_eq_of_forall_notMem J (by linarith [hj.2] : -C < z) fun t ht htJ =>
          h2 t ht.1 (ht.2.trans (by linarith [hj.1])) htJ
      have hr : rightLim b z = a + π * chiC κ :=
        Sec4.rightLim_eq_of_forall_notMem J (by linarith [hj.1] : z < -A) fun t ht htJ =>
          h2 t (by linarith [ht.1, hj.2]) ht.2 htJ
      exact (Finset.mem_filter.1 hzJ).2 (hl.trans hr.symm)
  have hfL : ∀ i, univ.filter (fun i' => (-xL) i' ≤ (-xL) i) =
      univ.filter (fun i' => xL i ≤ xL i') := by
    intro i; ext i'; simp
  have hfR : ∀ i, univ.filter (fun i' => (-xR) i ≤ (-xR) i') =
      univ.filter (fun i' => xR i' ≤ xR i) := by
    intro i; ext i'; simp
  have hxL0 : ∀ i, xL i ≤ 0 := (Theorem15.isOrderedForceWord_flowLine b J 0).2.1
  have hxR0 : ∀ i, 0 ≤ xR i := (Theorem15.isOrderedForceWord_flowLine b J 0).2.2.2
  have hL : ∀ i, κ / 2 - 2 ≤ ∑ i' ∈ univ.filter (fun i' => (-xR) i ≤ (-xR) i'), ρR i' := by
    intro i
    rw [hfR]
    obtain ⟨y, hy, hyJ, hS⟩ := exists_sum_flowLineRhoR_eq (κ := κ) hκ hb (hxR0 i)
    rw [hS]
    exact (Sec4.le_cumWeightRight_iff hκ).2 (h4 y ((hxR0 i).trans_lt hy) hyJ)
  have hR1 : ∀ i, (-xL) i < (-xL) iA →
      κ / 2 - 2 ≤ ∑ i' ∈ univ.filter (fun i' => (-xL) i' ≤ (-xL) i), ρL i' := by
    intro i hi
    rw [hxA] at hi
    simp only [Pi.neg_apply] at hi
    rw [hfL]
    obtain ⟨y, hy1, hy2, hyJ, hS⟩ := exists_sum_flowLineRhoL_eq (κ := κ) hκ hb (lo := -A) (by linarith)
      (hxL0 i)
    rw [hS]
    exact (Sec4.le_cumWeightLeft_iff hκ).2 (h1 y hy1 (hy2.trans_le (hxL0 i)) hyJ)
  have hR2 : Sec4.cumWeightLeft κ (a + π * chiC κ) =
      ∑ i' ∈ univ.filter (fun i' => (-xL) i' ≤ (-xL) iA), ρL i' := by
    rw [hfL]
    have hp : xL iA = -A := by rw [hxLdef, hiA]
    obtain ⟨y, hy1, hy2, hyJ, hS⟩ := exists_sum_flowLineRhoL_eq (κ := κ) hκ hb (lo := -C)
      (p := xL iA) (by rw [hp]; linarith) (by rw [hp]; linarith)
    rw [hS, h2 y hy1 (hp ▸ hy2) hyJ]
  have hRa : Sec4.cumWeightLeft κ (a + π * chiC κ) = κ / 2 - 3 - a / sleLambda κ := by
    rw [Sec4.cumWeightLeft_add_pi_mul_chiC hκ]; rfl
  have had : a / sleLambda κ < 1 := (div_lt_one hlam).2 ha'
  have had' : -1 < a / sleLambda κ := by
    rw [lt_div_iff₀ hlam]; linarith
  have hR3 : ∀ i, (-xL) iC ≤ (-xL) i →
      ∑ i' ∈ univ.filter (fun i' => (-xL) i' ≤ (-xL) i), ρL i' ≤ κ / 2 - 4 := by
    intro i hi
    rw [hxC] at hi
    simp only [Pi.neg_apply] at hi
    rw [hfL]
    obtain ⟨y, hy1, hy2, hyJ, hS⟩ := exists_sum_flowLineRhoL_eq (κ := κ) hκ hb (lo := xL i - 1)
      (by linarith) (hxL0 i)
    rw [hS]
    have hby := h3 y (by linarith) hyJ
    have e : b y = (b y - π * chiC κ) + π * chiC κ := by ring
    rw [e, Sec4.cumWeightLeft_add_pi_mul_chiC hκ]
    show κ / 2 - 3 - (b y - π * chiC κ) / sleLambda κ ≤ κ / 2 - 4
    have : 1 ≤ (b y - π * chiC κ) / sleLambda κ := by
      rw [le_div_iff₀ hlam]; linarith
    linarith
  have hac : (-xL) iA < (-xL) iC := by rw [hxA, hxC]; exact hAC
  have key := hseed (-xR) (-xL) ρR ρL P 𝓕 (-W) (fun i => -VR i) (fun i => -VL i) (-B) ζ iA iC hEr hD
    (by rw [hxA]; exact hA) hac hgap hL hR1 (by rw [← hR2, hRa]; linarith) (by rw [← hR2, hRa]; linarith)
    hR3
  filter_upwards [key, htr] with ω hω hη
  have hη' : IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) (fun t => LP.reflectC (η ω t)) :=
    LP.isGeneratingTrace_reflect hη
  obtain ⟨t, htζ, hav, x, hx1, hx2, hxt⟩ := hω _ hη'
  rw [hxA] at hx1
  rw [hxC] at hx2
  refine ⟨t, htζ, fun s hs z hz he => hav s hs (-z) (neg_ne_zero.2 hz) ?_, -x, by linarith, by linarith, ?_⟩
  · rw [he]; simp [LP.reflectC]
  · have := congrArg LP.reflectC hxt
    rw [LP.reflectC_reflectC] at this
    rw [this]; simp [LP.reflectC]

end Aux22ChartE

end Sec5

end InteractingSLE
