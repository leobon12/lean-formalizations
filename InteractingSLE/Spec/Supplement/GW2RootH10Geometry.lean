/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH10Heights

/-!
# Finite position cutoffs and separation for the root word

Continuation of PROVE-T14-GW2ROOT2. Ordered positions determine a cutoff
at any specified far level. Their finitely many nonzero coordinates have
a common positive separation from the driver, including empty sides and
coincident coordinates. No geometric separation of physical traces is used.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH10

/-- An outward ordered left vector splits into the labels strictly above
a far level and the labels at or below it. -/
theorem exists_antitone_cut {n : ℕ} (x : Fin n → ℝ) (hx : Antitone x)
    (a : ℝ) : ∃ m : ℕ, m ≤ n ∧
      (∀ i : Fin n, (i : ℕ) < m → a < x i) ∧
      ∀ i : Fin n, m ≤ (i : ℕ) → x i ≤ a := by
  let F := univ.filter (fun i => x i ≤ a)
  rcases F.eq_empty_or_nonempty with hF | hF
  · refine ⟨n, le_rfl, fun i _ => ?_, fun i hi => ?_⟩
    · by_contra h
      have hm : i ∈ F := mem_filter.2 ⟨mem_univ _, not_lt.1 h⟩
      rw [hF] at hm
      exact notMem_empty _ hm
    · exact False.elim (not_le_of_gt i.isLt hi)
  · let k := F.min' hF
    have hk : x k ≤ a := (mem_filter.1 (F.min'_mem hF)).2
    refine ⟨k, k.isLt.le, fun i hi => ?_, fun i hi => ?_⟩
    · by_contra h
      have hki : k ≤ i := F.min'_le i (mem_filter.2 ⟨mem_univ _, not_lt.1 h⟩)
      exact (not_le_of_gt hi) (show (k : ℕ) ≤ (i : ℕ) from hki)
    · exact (hx (show k ≤ i from hi)).trans hk

/-- The right-vector counterpart, by sign reversal of the same cutoff. -/
theorem exists_monotone_cut {n : ℕ} (x : Fin n → ℝ) (hx : Monotone x)
    (a : ℝ) : ∃ m : ℕ, m ≤ n ∧
      (∀ i : Fin n, (i : ℕ) < m → x i < a) ∧
      ∀ i : Fin n, m ≤ (i : ℕ) → a ≤ x i := by
  obtain ⟨m, hm, hnear, hfar⟩ :=
    exists_antitone_cut (fun i => -x i) (fun i j hij => neg_le_neg (hx hij)) (-a)
  exact ⟨m, hm, fun i hi => neg_lt_neg_iff.1 (hnear i hi),
    fun i hi => neg_le_neg_iff.1 (hfar i hi)⟩

/-- Every finite ordered word has one positive separation constant for
all nonzero positions. A dummy gap handles words consisting only of seeds. -/
theorem exists_positive_separation {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) :
    ∃ η : ℝ, 0 < η ∧ (∀ i, xL i ≠ 0 → xL i ≤ -η) ∧
      ∀ i, xR i ≠ 0 → η ≤ xR i := by
  let gap : Unit ⊕ (Fin nL ⊕ Fin nR) → ℝ
    | .inl _ => 1
    | .inr (.inl i) => if xL i = 0 then 1 else -xL i
    | .inr (.inr i) => if xR i = 0 then 1 else xR i
  have hne : (univ : Finset (Unit ⊕ (Fin nL ⊕ Fin nR))).Nonempty :=
    ⟨Sum.inl (), mem_univ _⟩
  let η := univ.inf' hne gap
  have hη : 0 < η := by
    apply (lt_inf'_iff hne).2
    intro i _
    rcases i with _ | (i | i)
    · exact zero_lt_one
    · change 0 < if xL i = 0 then 1 else -xL i
      split_ifs with hi
      · exact zero_lt_one
      · exact neg_pos.2 (lt_of_le_of_ne (hF.2.1 i) hi)
    · change 0 < if xR i = 0 then 1 else xR i
      split_ifs with hi
      · exact zero_lt_one
      · exact lt_of_le_of_ne (hF.2.2.2 i) (Ne.symm hi)
  refine ⟨η, hη, fun i hi => ?_, fun i hi => ?_⟩
  · have h := inf'_le gap (mem_univ (Sum.inr (Sum.inl i)))
    change η ≤ if xL i = 0 then 1 else -xL i at h
    rw [ite_eq_right hi] at h
    linarith only [h]
  · have h := inf'_le gap (mem_univ (Sum.inr (Sum.inr i)))
    change η ≤ if xR i = 0 then 1 else xR i at h
    rwa [ite_eq_right hi] at h

end InteractingSLE.Theorem14.GW2TipSystem.RootH10
