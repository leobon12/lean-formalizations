/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2

/-!
# Uniform DS1 bounds from qualitative finite-word convergence

Continuation of PROVE-T14-GW2ROOT2. Strict inner partial sums of the limiting
word and convergence of the finite weight vectors give a common positive
margin and weight bound on a tail. These quantitative DS1 bounds need not
be assumed separately when constructing a near-crossing family.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset

namespace InteractingSLE.Theorem14.GW2TipSystem.RootW8

open Supp12.DS2

/-- A convergent finite-force word with strictly admissible limiting inner
partial sums satisfies DS1 with fixed positive margin on a tail, including
the limiting word. The positions and far cutoffs are unchanged. -/
theorem exists_ds1_tail {nL nR mL mR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρLs : ℕ → Fin nL → ℝ} {ρRs : ℕ → Fin nR → ℝ}
    {ρL₀ : Fin nL → ℝ} {ρR₀ : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR)
    (hL : ∀ i : Fin nL, (i : ℕ) < mL →
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i), ρL₀ j)
    (hR : ∀ i : Fin nR, (i : ℕ) < mR →
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i), ρR₀ j)
    (hρL : Tendsto ρLs atTop (𝓝 ρL₀)) (hρR : Tendsto ρRs atTop (𝓝 ρR₀)) :
    ∃ Rw ε : ℝ, 0 < ε ∧ IsDS1Word mL mR Rw ε xL xR ρL₀ ρR₀ ∧
      ∃ N : ℕ, ∀ m ≥ N, IsDS1Word mL mR Rw ε xL xR (ρLs m) (ρRs m) := by
  classical
  let gapL : Fin nL → ℝ := fun i => (∑ j ∈ univ.filter (fun j => j ≤ i), ρL₀ j) + 2
  let gapR : Fin nR → ℝ := fun i => (∑ j ∈ univ.filter (fun j => j ≤ i), ρR₀ j) + 2
  let gap : Unit ⊕ (Fin nL ⊕ Fin nR) → ℝ
    | .inl _ => 1
    | .inr (.inl i) => if (i : ℕ) < mL then gapL i else 1
    | .inr (.inr i) => if (i : ℕ) < mR then gapR i else 1
  have hne : (univ : Finset (Unit ⊕ (Fin nL ⊕ Fin nR))).Nonempty :=
    ⟨Sum.inl (), mem_univ _⟩
  let μ : ℝ := univ.inf' hne gap
  have hμ : 0 < μ := by
    apply (lt_inf'_iff hne).2
    intro i _
    rcases i with _ | (i | i)
    · exact zero_lt_one
    · change 0 < if (i : ℕ) < mL then gapL i else 1
      split_ifs with hi
      · have h := hL i hi
        dsimp [gapL]
        linarith only [h]
      · exact zero_lt_one
    · change 0 < if (i : ℕ) < mR then gapR i else 1
      split_ifs with hi
      · have h := hR i hi
        dsimp [gapR]
        linarith only [h]
      · exact zero_lt_one
  let ε : ℝ := μ / 2
  have hε : 0 < ε := half_pos hμ
  have hεL : ∀ i : Fin nL, (i : ℕ) < mL → ε < gapL i := by
    intro i hi
    have h := inf'_le gap (mem_univ (Sum.inr (Sum.inl i)))
    change μ ≤ if (i : ℕ) < mL then gapL i else 1 at h
    rw [ite_eq_left hi] at h
    exact (half_lt_self hμ).trans_le h
  have hεR : ∀ i : Fin nR, (i : ℕ) < mR → ε < gapR i := by
    intro i hi
    have h := inf'_le gap (mem_univ (Sum.inr (Sum.inr i)))
    change μ ≤ if (i : ℕ) < mR then gapR i else 1 at h
    rw [ite_eq_left hi] at h
    exact (half_lt_self hμ).trans_le h
  let Rw : ℝ := (∑ i, |ρL₀ i|) + (∑ i, |ρR₀ i|) + 1
  have hRwL : ∀ i, |ρL₀ i| < Rw := by
    intro i
    have h := single_le_sum (fun j _ => abs_nonneg (ρL₀ j)) (mem_univ i)
    have hR0 : 0 ≤ ∑ j, |ρR₀ j| := sum_nonneg fun _ _ => abs_nonneg _
    dsimp [Rw]
    linarith only [h, hR0]
  have hRwR : ∀ i, |ρR₀ i| < Rw := by
    intro i
    have h := single_le_sum (fun j _ => abs_nonneg (ρR₀ j)) (mem_univ i)
    have hL0 : 0 ≤ ∑ j, |ρL₀ j| := sum_nonneg fun _ _ => abs_nonneg _
    dsimp [Rw]
    linarith only [h, hL0]
  have hbL : ∀ᶠ m in atTop, ∀ i, |ρLs m i| ≤ Rw := by
    rw [eventually_all]
    intro i
    exact ((tendsto_pi_nhds.1 hρL i).abs.eventually (gt_mem_nhds (hRwL i))).mono
      fun _ h => h.le
  have hbR : ∀ᶠ m in atTop, ∀ i, |ρRs m i| ≤ Rw := by
    rw [eventually_all]
    intro i
    exact ((tendsto_pi_nhds.1 hρR i).abs.eventually (gt_mem_nhds (hRwR i))).mono
      fun _ h => h.le
  have hmL : ∀ᶠ m in atTop, ∀ i : Fin nL, (i : ℕ) < mL →
      ε ≤ (∑ j ∈ univ.filter (fun j => j ≤ i), ρLs m j) + 2 := by
    rw [eventually_all]
    intro i
    by_cases hi : (i : ℕ) < mL
    · have hc : Tendsto (fun m => (∑ j ∈ univ.filter (fun j => j ≤ i), ρLs m j) + 2)
          atTop (𝓝 (gapL i)) :=
        (tendsto_finsetSum _ fun j _ => tendsto_pi_nhds.1 hρL j).add_const 2
      exact (hc.eventually (lt_mem_nhds (hεL i hi))).mono fun _ h _ => h.le
    · exact Eventually.of_forall fun _ h => False.elim (hi h)
  have hmR : ∀ᶠ m in atTop, ∀ i : Fin nR, (i : ℕ) < mR →
      ε ≤ (∑ j ∈ univ.filter (fun j => j ≤ i), ρRs m j) + 2 := by
    rw [eventually_all]
    intro i
    by_cases hi : (i : ℕ) < mR
    · have hc : Tendsto (fun m => (∑ j ∈ univ.filter (fun j => j ≤ i), ρRs m j) + 2)
          atTop (𝓝 (gapR i)) :=
        (tendsto_finsetSum _ fun j _ => tendsto_pi_nhds.1 hρR j).add_const 2
      exact (hc.eventually (lt_mem_nhds (hεR i hi))).mono fun _ h _ => h.le
    · exact Eventually.of_forall fun _ h => False.elim (hi h)
  refine ⟨Rw, ε, hε, ⟨hF, fun i => (hRwL i).le, fun i => (hRwR i).le,
    fun i hi => (hεL i hi).le, fun i hi => (hεR i hi).le⟩, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hbL.and hbR).and (hmL.and hmR))
  exact ⟨N, fun m hm => ⟨hF, (hN m hm).1.1, (hN m hm).1.2,
    (hN m hm).2.1, (hN m hm).2.2⟩⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootW8
