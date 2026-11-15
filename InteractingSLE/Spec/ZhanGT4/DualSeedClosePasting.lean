/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalTaylor
import InteractingSLE.Stochastic.ItoAdaptedStop

/-!
# Finite pasting of the localized logarithmic Taylor steps

Packet PROVE-ZHAN-GT4-A22. Telescope the actual logarithm and its time
integral on a regular spatial piece. Separately bound the finitely many
cells crossing piece boundaries on any monotone grid, including the
clamped dyadic grid. These deterministic lemmas do not assert that the
concrete seed bands have already supplied all the regular pieces.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.ZhanGT4

/-- Paste actual Taylor steps on one regular piece. Both the field values
and the integrals telescope, so the conclusion is a finite expansion of
the original logarithm, with its original derivatives. -/
theorem IsLogField.seed_log_paste
    {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {b c y ρ K Cχ : ℝ}
    (h : IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c y ρ K)
    (hC : 0 ≤ Cχ) (hχ : ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ Cχ)
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc b c))
    (hnear : ∀ u ∈ Icc b c, |β u - y| < ρ)
    (p : ℕ → ℝ) (N : ℕ) (hp : Monotone p)
    (hpc : ∀ k ≤ N, p k ∈ Icc b c) :
    |ℓ (p N) (β (p N)) - ℓ (p 0) (β (p 0)) -
        (∫ u in p 0..p N, (ℓt u (β u) + 1 / 2 * ℓxx u (β u))) -
        (∑ k ∈ Finset.range N, ℓx (p k) (β (p k)) * (β (p (k + 1)) - β (p k))) -
        (∑ k ∈ Finset.range N, 1 / 2 * ℓxx (p k) (β (p k)) *
          ((β (p (k + 1)) - β (p k)) ^ 2 - (p (k + 1) - p k)))| ≤
      (8 * Cχ * K) * (∑ k ∈ Finset.range N, |β (p (k + 1)) - β (p k)| ^ 3) +
        ∑ k ∈ Finset.range N, Ito.fieldStepRem (seedLogCutT ℓt y ρ)
          (seedLogCut2 ℓ ℓx ℓxx y ρ) β (p k) (p (k + 1)) := by
  have hmap : MapsTo (fun u => (u, β u)) (Icc b c)
      (Icc b c ×ˢ {x | |x - y| < 3 * ρ}) := by
    intro u hu
    exact ⟨hu, (hnear u hu).trans (by linarith [h.pos])⟩
  have hg : ContinuousOn (fun u => ℓt u (β u) + 1 / 2 * ℓxx u (β u)) (Icc b c) :=
    (h.contT.comp (continuousOn_id.prodMk hβ) hmap).add
      (continuousOn_const.mul (h.contXX.comp (continuousOn_id.prodMk hβ) hmap))
  have hi := intervalIntegral.sum_integral_adjacent_intervals (n := N) (μ := volume) (a := p)
    (f := fun u => ℓt u (β u) + 1 / 2 * ℓxx u (β u)) (fun k hk =>
      (hg.mono (Icc_subset_Icc (hpc k hk.le).1 (hpc (k + 1) hk).2)).intervalIntegrable_of_Icc
        (hp (Nat.le_succ k)))
  let E : ℕ → ℝ := fun k => ℓ (p (k + 1)) (β (p (k + 1))) - ℓ (p k) (β (p k)) -
    (∫ u in p k..p (k + 1), (ℓt u (β u) + 1 / 2 * ℓxx u (β u))) -
    ℓx (p k) (β (p k)) * (β (p (k + 1)) - β (p k)) -
    1 / 2 * ℓxx (p k) (β (p k)) *
      ((β (p (k + 1)) - β (p k)) ^ 2 - (p (k + 1) - p k))
  have htel : (∑ k ∈ Finset.range N, ℓ (p (k + 1)) (β (p (k + 1)))) -
      (∑ k ∈ Finset.range N, ℓ (p k) (β (p k))) =
      ℓ (p N) (β (p N)) - ℓ (p 0) (β (p 0)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_range_sub (fun k => ℓ (p k) (β (p k))) N
  have hE (k : ℕ) (hk : k ∈ Finset.range N) : |E k| ≤
      (8 * Cχ * K) * |β (p (k + 1)) - β (p k)| ^ 3 +
        Ito.fieldStepRem (seedLogCutT ℓt y ρ) (seedLogCut2 ℓ ℓx ℓxx y ρ) β (p k) (p (k + 1)) := by
    have hkN := Finset.mem_range.1 hk
    have hsub := Icc_subset_Icc (hpc k hkN.le).1 (hpc (k + 1) hkN).2
    exact h.seed_log_taylor_step hC hχ (hpc k hkN.le).1 (hp (Nat.le_succ k))
      (hpc (k + 1) hkN).2 (hβ.mono hsub) (fun u hu => hnear u (hsub hu))
  have hs := (Finset.abs_sum_le_sum_abs E (Finset.range N)).trans (Finset.sum_le_sum hE)
  simp only [E, Finset.sum_sub_distrib, htel, hi] at hs
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hs

/-- At most one cell of a monotone grid strictly crosses a fixed boundary. -/
theorem seed_unique_crossing_cell {p : ℕ → ℝ} (hp : Monotone p) {σ : ℝ} {k j : ℕ}
    (hk : p k < σ ∧ σ < p (k + 1)) (hj : p j < σ ∧ σ < p (j + 1)) : k = j := by
  apply le_antisymm
  · by_contra hh
    have h := hp (Nat.succ_le_of_lt (lt_of_not_ge hh))
    linarith [hk.1, hj.2]
  · by_contra hh
    have h := hp (Nat.succ_le_of_lt (lt_of_not_ge hh))
    linarith [hj.1, hk.2]

/-- Sum the boundary-cell errors without a factor equal to the number of
grid cells. This works for the partial cells at the clamped horizon too. -/
theorem seed_sum_boundary_cells_le {p : ℕ → ℝ} (hp : Monotone p)
    (cuts : Finset ℝ) (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    (∑ k ∈ Finset.range N, ∑ σ ∈ cuts,
      if p k < σ ∧ σ < p (k + 1) then M else 0) ≤ cuts.card * M := by
  classical
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _σ ∈ cuts, M := by
        apply Finset.sum_le_sum
        intro σ _
        exact Ito.sum_ite_le_of_unique hM (fun _ _ _ => le_rfl)
          (fun _ _ hk hj => seed_unique_crossing_cell hp hk hj)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end InteractingSLE.ZhanGT4
