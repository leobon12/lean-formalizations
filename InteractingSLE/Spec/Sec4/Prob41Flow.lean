/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.PartialSums
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.flowLineXL
import InteractingSLE.Frozen.Spec.flowLineXR
import InteractingSLE.Frozen.Spec.flowLineRhoL
import InteractingSLE.Frozen.Spec.flowLineRhoR
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The flow-line force word reproduces the boundary data (Remark 4.1 for flow lines)

Packet PROVE-SEC4-A3. The hypotheses of Lemmas 4.3, 4.5, 4.6 and Aux. lemma 22 are stated on the boundary data
of the field ("at most `−λ + πχ` to the left of `0` and at least `λ − πχ` to the right of `0`", Remark 4.1, p. 103),
while noncollision (Aux. lemma 6) is stated on the partial sums of the force word. The frozen `flowLineRhoL`
docstring asserts that the flow-line word's boundary data equals `b` off the marks; this file proves it (at the
seed `x = 0`, angle `θ = 0`) and derives the partial-sum hypothesis from Remark 4.1's boundary condition:

* `eq_of_forall_notMem_of_isPiecewiseConstant`: piecewise-constant data is constant on a closed interval
  free of jump candidates; `leftLim_eq_of_forall`, `rightLim_eq_of_forall`: one-sided limits of locally
  constant data;
* `sub_eq_sum_of_isPiecewiseConstant`: `b v − b u = ∑_{z ∈ J ∩ (u, v)} (b(z⁺) − b(z⁻))` (telescoping
  over the jumps);
* `forceBoundaryData_flowLine`: the force-word boundary data of the flow line from `0` (angle `0`) equals `b`
  at every point `x ≠ 0` off the jump set;
* `hasAdmissiblePartialSums_flowLine`: Remark 4.1's boundary condition on `b` gives the noncollision
  hypothesis `HasAdmissiblePartialSums` of the flow-line word.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset

namespace InteractingSLE

namespace Sec4

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-! ### Piecewise-constant data -/

/-- Piecewise-constant data is constant on a closed interval free of jump candidates. -/
theorem eq_of_forall_notMem_of_isPiecewiseConstant
    (hb : IsPiecewiseConstantBoundaryData b J) {u v : ℝ} (huv : u ≤ v)
    (hJ : ∀ z ∈ Set.Icc u v, z ∉ J) : b v = b u := by
  have hd : ∀ z ∈ Set.Icc u v, HasDerivAt b 0 z := fun z hz =>
    (hasDerivAt_const z (b z)).congr_of_eventuallyEq (hb z (hJ z hz))
  exact constant_of_has_deriv_right_zero (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hd z (Ico_subset_Icc_self hz)).hasDerivWithinAt) v ⟨huv, le_rfl⟩

/-- The left limit of data that is constant just left of `z`. -/
theorem leftLim_eq_of_forall {a z c : ℝ} (haz : a < z) (h : ∀ t ∈ Set.Ioo a z, b t = c) :
    leftLim b z = c := by
  unfold PiecewiseConstantBoundaryData.leftLim
  refine Filter.Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT haz] with t ht using (h t ht).symm

/-- The right limit of data that is constant just right of `z`. -/
theorem rightLim_eq_of_forall {z a c : ℝ} (hza : z < a) (h : ∀ t ∈ Set.Ioo z a, b t = c) :
    rightLim b z = c := by
  unfold PiecewiseConstantBoundaryData.rightLim
  refine Filter.Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hza] with t ht using (h t ht).symm

/-- Data free of jump candidates on `(a, c)` is constant there. -/
theorem eq_of_mem_Ioo_of_isPiecewiseConstant (hb : IsPiecewiseConstantBoundaryData b J)
    {a c : ℝ} (hJ : ∀ z ∈ J, z ∉ Set.Ioo a c) {s t : ℝ} (hs : s ∈ Set.Ioo a c)
    (ht : t ∈ Set.Ioo a c) : b t = b s := by
  rcases le_total s t with hst | hts
  · exact eq_of_forall_notMem_of_isPiecewiseConstant hb hst fun z hz hzJ =>
      hJ z hzJ ⟨hs.1.trans_le hz.1, hz.2.trans_lt ht.2⟩
  · exact (eq_of_forall_notMem_of_isPiecewiseConstant hb hts fun z hz hzJ =>
      hJ z hzJ ⟨ht.1.trans_le hz.1, hz.2.trans_lt hs.2⟩).symm

/-- **Telescoping over the jumps.** For piecewise-constant data and `u < v` off the jump candidates,
`b v − b u = ∑_{z ∈ J ∩ (u, v)} (b(z⁺) − b(z⁻))` (induction on the number of candidates in `(u, v)`). -/
theorem sub_eq_sum_of_isPiecewiseConstant (hb : IsPiecewiseConstantBoundaryData b J) :
    ∀ (n : ℕ) {u v : ℝ}, u < v → u ∉ J → v ∉ J →
      (J.filter fun z => u < z ∧ z < v).card = n →
      b v - b u = ∑ z ∈ J.filter (fun z => u < z ∧ z < v), (rightLim b z - leftLim b z) := by
  intro n
  induction n with
  | zero =>
    intro u v huv hu hv hcard
    rw [Finset.card_eq_zero] at hcard
    rw [hcard, Finset.sum_empty, sub_eq_zero]
    refine eq_of_forall_notMem_of_isPiecewiseConstant hb huv.le fun z hz hzJ => ?_
    rcases eq_or_lt_of_le hz.1 with h | h
    · exact hu (h ▸ hzJ)
    rcases eq_or_lt_of_le hz.2 with h' | h'
    · exact hv (h' ▸ hzJ)
    have hmem : z ∈ J.filter (fun z => u < z ∧ z < v) := Finset.mem_filter.2 ⟨hzJ, h, h'⟩
    rw [hcard] at hmem
    exact Finset.notMem_empty z hmem
  | succ n ih =>
    intro u v huv hu hv hcard
    set F := J.filter (fun z => u < z ∧ z < v) with hF
    have hne : F.Nonempty := Finset.card_pos.1 (by rw [hcard]; exact Nat.succ_pos n)
    set z₁ := F.min' hne with hz₁
    have hz₁F : z₁ ∈ F := F.min'_mem hne
    obtain ⟨hz₁J, hz₁u, hz₁v⟩ := Finset.mem_filter.1 hz₁F
    set T := J.filter (fun z => z₁ < z ∧ z < v) with hT
    set m := (insert v T).min' (Finset.insert_nonempty v T) with hm
    have hmv : m ≤ v := (insert v T).min'_le v (Finset.mem_insert_self v T)
    have hz₁m : z₁ < m := by
      have hmmem : m ∈ insert v T := (insert v T).min'_mem (Finset.insert_nonempty v T)
      rcases Finset.mem_insert.1 hmmem with h | h
      · rw [h]; exact hz₁v
      · exact (Finset.mem_filter.1 h).2.1
    have hnoJ : ∀ z ∈ J, z ∉ Set.Ioo z₁ m := fun z hzJ hz => by
      have hzT : z ∈ T := Finset.mem_filter.2 ⟨hzJ, hz.1, hz.2.trans_le hmv⟩
      have := (insert v T).min'_le z (Finset.mem_insert_of_mem hzT)
      linarith [hz.2]
    set u' := (z₁ + m) / 2 with hu'
    have hu'1 : z₁ < u' := by rw [hu']; linarith
    have hu'2 : u' < m := by rw [hu']; linarith
    have hu'J : u' ∉ J := fun h => hnoJ u' h ⟨hu'1, hu'2⟩
    have hu'v : u' < v := lt_of_lt_of_le hu'2 hmv
    have hF' : J.filter (fun z => u' < z ∧ z < v) = F.erase z₁ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase, hF]
      constructor
      · rintro ⟨hzJ, h1, h2⟩
        refine ⟨fun h => ?_, hzJ, by linarith, h2⟩
        rw [h] at h1
        linarith
      · rintro ⟨hne', hzJ, h1, h2⟩
        refine ⟨hzJ, ?_, h2⟩
        have hle : z₁ ≤ z := F.min'_le z (Finset.mem_filter.2 ⟨hzJ, h1, h2⟩)
        have hlt : z₁ < z := lt_of_le_of_ne hle (Ne.symm hne')
        by_contra hz
        exact hnoJ z hzJ ⟨hlt, lt_of_le_of_lt (not_lt.1 hz) hu'2⟩
    have hcard' : (J.filter (fun z => u' < z ∧ z < v)).card = n := by
      rw [hF', Finset.card_erase_of_mem hz₁F, hcard]
      rfl
    have hih := ih hu'v hu'J hv hcard'
    have hr : rightLim b z₁ = b u' := rightLim_eq_of_forall hz₁m fun t ht =>
      eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ ⟨hu'1, hu'2⟩ ht
    have hnoJ' : ∀ z ∈ J, z ∉ Set.Ioo u z₁ := fun z hzJ hz => by
      have := F.min'_le z (Finset.mem_filter.2 ⟨hzJ, hz.1, hz.2.trans hz₁v⟩)
      linarith [hz.2]
    have hl : leftLim b z₁ = b u := leftLim_eq_of_forall hz₁u fun t ht =>
      eq_of_forall_notMem_of_isPiecewiseConstant hb ht.1.le fun z hz hzJ => by
        rcases eq_or_lt_of_le hz.1 with h | h
        · exact hu (h ▸ hzJ)
        · exact hnoJ' z hzJ ⟨h, lt_of_le_of_lt hz.2 ht.2⟩
    rw [← Finset.insert_erase hz₁F, Finset.sum_insert (Finset.notMem_erase z₁ F), ← hF', ← hih,
      hr, hl]
    ring

/-- **Left telescoping to the seed.** For `x < 0` off the jump candidates,
`b x = b(0⁻) − ∑_{z ∈ J ∩ (x, 0)} (b(z⁺) − b(z⁻))`. -/
theorem eq_leftLim_sub_sum_of_isPiecewiseConstant (hb : IsPiecewiseConstantBoundaryData b J)
    {x : ℝ} (hx : x < 0) (hxJ : x ∉ J) :
    b x = leftLim b 0 - ∑ z ∈ J.filter (fun z => x < z ∧ z < 0), (rightLim b z - leftLim b z) := by
  set S := insert x (J.filter (· < 0)) with hS
  set m := S.max' (Finset.insert_nonempty _ _) with hm
  have hxm : x ≤ m := S.le_max' x (Finset.mem_insert_self _ _)
  have hm0 : m < 0 := by
    have hmem : m ∈ S := S.max'_mem _
    rcases Finset.mem_insert.1 hmem with h | h
    · rw [h]; exact hx
    · exact (Finset.mem_filter.1 h).2
  have hnoJ : ∀ z ∈ J, z ∉ Set.Ioo m 0 := fun z hzJ hz => by
    have := S.le_max' z (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hzJ, hz.2⟩))
    linarith [hz.1]
  set v := m / 2 with hv
  have hmv : m < v := by rw [hv]; linarith
  have hv0 : v < 0 := by rw [hv]; linarith
  have hvJ : v ∉ J := fun h => hnoJ v h ⟨hmv, hv0⟩
  have hl : leftLim b 0 = b v := leftLim_eq_of_forall hm0 fun t ht =>
    eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ ⟨hmv, hv0⟩ ht
  have hfilt : J.filter (fun z => x < z ∧ z < v) = J.filter (fun z => x < z ∧ z < 0) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, h3.trans hv0⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      by_contra h
      exact hnoJ z h1 ⟨lt_of_lt_of_le hmv (not_lt.1 h), h3⟩
  have h := sub_eq_sum_of_isPiecewiseConstant hb _ (lt_of_le_of_lt hxm hmv) hxJ hvJ rfl
  rw [hfilt] at h
  rw [hl]
  linarith

/-- **Right telescoping from the seed.** For `x > 0` off the jump candidates,
`b x = b(0⁺) + ∑_{z ∈ J ∩ (0, x)} (b(z⁺) − b(z⁻))`. -/
theorem eq_rightLim_add_sum_of_isPiecewiseConstant (hb : IsPiecewiseConstantBoundaryData b J)
    {x : ℝ} (hx : 0 < x) (hxJ : x ∉ J) :
    b x = rightLim b 0 + ∑ z ∈ J.filter (fun z => 0 < z ∧ z < x), (rightLim b z - leftLim b z) := by
  set S := insert x (J.filter (0 < ·)) with hS
  set m := S.min' (Finset.insert_nonempty _ _) with hm
  have hmx : m ≤ x := S.min'_le x (Finset.mem_insert_self _ _)
  have hm0 : 0 < m := by
    have hmem : m ∈ S := S.min'_mem _
    rcases Finset.mem_insert.1 hmem with h | h
    · rw [h]; exact hx
    · exact (Finset.mem_filter.1 h).2
  have hnoJ : ∀ z ∈ J, z ∉ Set.Ioo 0 m := fun z hzJ hz => by
    have := S.min'_le z (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hzJ, hz.1⟩))
    linarith [hz.2]
  set u := m / 2 with hu
  have hum : u < m := by rw [hu]; linarith
  have hu0 : 0 < u := by rw [hu]; linarith
  have huJ : u ∉ J := fun h => hnoJ u h ⟨hu0, hum⟩
  have hr : rightLim b 0 = b u := rightLim_eq_of_forall hm0 fun t ht =>
    eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ ⟨hu0, hum⟩ ht
  have hfilt : J.filter (fun z => u < z ∧ z < x) = J.filter (fun z => 0 < z ∧ z < x) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, hu0.trans h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      by_contra h
      exact hnoJ z h1 ⟨h2, lt_of_le_of_lt (not_lt.1 h) hum⟩
  have h := sub_eq_sum_of_isPiecewiseConstant hb _ (lt_of_lt_of_le hum hmx) huJ hxJ rfl
  rw [hfilt] at h
  rw [hr]
  linarith

/-! ### Sums over the flow-line word -/

/-- Splitting off the seed mark of a `Fin.cons` word (left prefixes). -/
theorem sum_filter_lt_cons {n : ℕ} (p₀ a : ℝ) (p f : Fin n → ℝ) (x : ℝ) :
    ∑ i ∈ univ.filter (fun i => x < (Fin.cons p₀ p : Fin (n + 1) → ℝ) i),
        (Fin.cons a f : Fin (n + 1) → ℝ) i =
      (if x < p₀ then a else 0) + ∑ j ∈ univ.filter (fun j => x < p j), f j := by
  rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Splitting off the seed mark of a `Fin.cons` word (right prefixes). -/
theorem sum_filter_le_cons {n : ℕ} (p₀ a : ℝ) (p f : Fin n → ℝ) (x : ℝ) :
    ∑ i ∈ univ.filter (fun i => (Fin.cons p₀ p : Fin (n + 1) → ℝ) i ≤ x),
        (Fin.cons a f : Fin (n + 1) → ℝ) i =
      (if p₀ ≤ x then a else 0) + ∑ j ∈ univ.filter (fun j => p j ≤ x), f j := by
  rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Reindexing a sum over the sorted enumeration of a finite set. -/
theorem sum_filter_orderEmbOfFin (S : Finset ℝ) (P : ℝ → Prop) [DecidablePred P] (g : ℝ → ℝ) :
    ∑ j ∈ univ.filter (fun j : Fin S.card => P (S.orderEmbOfFin rfl j)), g (S.orderEmbOfFin rfl j) =
      ∑ z ∈ S.filter P, g z := by
  rw [Finset.sum_filter, Finset.sum_filter]
  conv_rhs => rw [← S.map_orderEmbOfFin_univ rfl, Finset.sum_map]
  rfl

/-- Reindexing a sum over the reversed sorted enumeration of a finite set. -/
theorem sum_filter_orderEmbOfFin_rev (S : Finset ℝ) (P : ℝ → Prop) [DecidablePred P]
    (g : ℝ → ℝ) :
    ∑ j ∈ univ.filter (fun j : Fin S.card => P (S.orderEmbOfFin rfl (Fin.rev j))),
        g (S.orderEmbOfFin rfl (Fin.rev j)) =
      ∑ z ∈ S.filter P, g z := by
  rw [← sum_filter_orderEmbOfFin S P g, Finset.sum_filter, Finset.sum_filter]
  exact Equiv.sum_comp Fin.revPerm
    (fun j => if P (S.orderEmbOfFin rfl j) then g (S.orderEmbOfFin rfl j) else 0)

/-- Sums over the genuine jumps equal sums over all jump candidates (non-genuine candidates contribute
`b(z⁺) − b(z⁻) = 0`). -/
theorem sum_jumpSet_filter (P : ℝ → Prop) [DecidablePred P] :
    ∑ z ∈ (jumpSet b J).filter P, (rightLim b z - leftLim b z) =
      ∑ z ∈ J.filter P, (rightLim b z - leftLim b z) := by
  refine Finset.sum_subset (fun z hz => ?_) fun z hz hzn => ?_
  · obtain ⟨hzJ, hP⟩ := Finset.mem_filter.1 hz
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hzJ).1, hP⟩
  · obtain ⟨hzJ, hP⟩ := Finset.mem_filter.1 hz
    have : ¬ (leftLim b z ≠ rightLim b z) := fun hne =>
      hzn (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hzJ, hne⟩, hP⟩)
    rw [not_not] at this
    rw [this, sub_self]

/-! ### The flow-line word reproduces the boundary data -/

/-- Left prefix sums of the flow-line word from `0` (angle `0`). -/
theorem sum_filter_flowLineXL {k : ℝ} {x : ℝ} (hx : x < 0) :
    ∑ i ∈ univ.filter (fun i => x < flowLineXL b J 0 i), flowLineRhoL k b J 0 0 i =
      (-(leftLim b 0) / sleLambda k - 1) +
        (∑ z ∈ J.filter (fun z => x < z ∧ z < 0), (rightLim b z - leftLim b z)) / sleLambda k := by
  unfold flowLineXL flowLineRhoL flowLineNL
  rw [sum_filter_lt_cons]
  simp only [hx, ↓reduceIte, sub_zero, zero_mul, add_zero]
  have h := sum_filter_orderEmbOfFin_rev ((jumpSet b J).filter (· < 0)) (fun z => x < z)
    (fun z => (rightLim b z - leftLim b z) / sleLambda k)
  rw [h, ← Finset.sum_div, Finset.filter_filter, sum_jumpSet_filter]
  congr 3
  exact Finset.filter_congr fun z _ => and_comm

/-- Right prefix sums of the flow-line word from `0` (angle `0`), at a point `x > 0` off the jump
candidates. -/
theorem sum_filter_flowLineXR {k : ℝ} {x : ℝ} (hx : 0 < x) (hxJ : x ∉ J) :
    ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ x), flowLineRhoR k b J 0 0 i =
      (rightLim b 0 / sleLambda k - 1) +
        (∑ z ∈ J.filter (fun z => 0 < z ∧ z < x), (rightLim b z - leftLim b z)) / sleLambda k := by
  unfold flowLineXR flowLineRhoR flowLineNR
  rw [sum_filter_le_cons]
  simp only [hx.le, ↓reduceIte, sub_zero, zero_mul, add_zero]
  have h := sum_filter_orderEmbOfFin ((jumpSet b J).filter (0 < ·)) (fun z => z ≤ x)
    (fun z => (rightLim b z - leftLim b z) / sleLambda k)
  rw [h, ← Finset.sum_div, Finset.filter_filter, sum_jumpSet_filter]
  congr 3
  refine Finset.filter_congr fun z hz => and_congr_right fun _ => ?_
  exact ⟨fun h => lt_of_le_of_ne h fun he => hxJ (he ▸ hz), le_of_lt⟩

/-- **The flow-line word reproduces the boundary data** (the identity asserted in the frozen
`flowLineRhoL`/`flowLineRhoR` docstrings, at the seed `0` and angle `0`): off the jump candidates and the
seed, the force-word boundary data of Theorem 1.1 of the flow line of `b` is `b`. -/
theorem forceBoundaryData_flowLine {k : ℝ} (hk : 0 < k) (hb : IsPiecewiseConstantBoundaryData b J)
    {x : ℝ} (hx0 : x ≠ 0) (hxJ : x ∉ J) :
    forceBoundaryData k (flowLineRhoL k b J 0 0) (flowLineRhoR k b J 0 0) (flowLineXL b J 0)
      (flowLineXR b J 0) x = b x := by
  have hΛ : sleLambda k ≠ 0 := (sleLambda_pos hk).ne'
  have hL : Real.pi / Real.sqrt k = sleLambda k := rfl
  unfold forceBoundaryData
  rw [hL]
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · simp only [hx, ↓reduceIte]
    rw [sum_filter_flowLineXL hx, eq_leftLim_sub_sum_of_isPiecewiseConstant hb hx hxJ]
    field_simp
    ring
  · simp only [not_lt.2 hx.le, ↓reduceIte]
    rw [sum_filter_flowLineXR hx hxJ, eq_rightLim_add_sum_of_isPiecewiseConstant hb hx hxJ]
    field_simp
    ring

open Real in
/-- **Remark 4.1 for flow lines.** If the boundary data `b` is at most `−Λ + πX` left of the seed and at least
`Λ − πX` right of it (off the jump candidates), the flow-line word from `0` (angle `0`) has every side partial
sum at least `k/2 − 2`: the noncollision hypothesis of Aux. lemmas 6–7. -/
theorem hasAdmissiblePartialSums_flowLine {k : ℝ} (hk : 0 < k)
    (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ x : ℝ, x < 0 → x ∉ J → b x ≤ -sleLambda k + π * QuantumZipper.chiC k)
    (hR : ∀ x : ℝ, 0 < x → x ∉ J → sleLambda k - π * QuantumZipper.chiC k ≤ b x) :
    HasAdmissiblePartialSums k (flowLineRhoL k b J 0 0) (flowLineRhoR k b J 0 0)
      (flowLineXL b J 0) (flowLineXR b J 0) := by
  refine hasAdmissiblePartialSums_of_forall_not_mem hk (insert 0 J) (fun x hx hxE _ => ?_)
    (fun x hx hxE _ => ?_)
  · have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [forceBoundaryData_flowLine hk hb hx.ne hxJ]
    exact hL x hx hxJ
  · have hx0 : x ≠ 0 := fun h => hxE (h ▸ Finset.mem_insert_self 0 J)
    have hxJ : x ∉ J := fun h => hxE (Finset.mem_insert_of_mem h)
    rw [forceBoundaryData_flowLine hk hb hx0 hxJ]
    exact hR x (lt_of_le_of_ne hx (Ne.symm hx0)) hxJ

end Sec4

end InteractingSLE
