/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgFrame

/-!
# G3 large direction: the frozen marked configuration

The protected point may coincide with the ordinary mark. Moving it to `q + dd`
and halving its radius gives the strict inequalities required by the frozen law.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open QuantumZipper (fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Marg A1SeedField A1EightSeed A1EightFin A1G3Calc A1Common A1Asm
  A1G3Law A1ELaw A1G3RR A1G3Id

/-- Extract the protected point and finite mark bounds in the translated, large-curve frame. -/
theorem frozen_mark_frame {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd S s : ℝ}
    (hpp : IsProtectedPair H₁ H₂ δ p q dd) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hS : 0 < S)
    (hK : fwdHull W S ⊆ H₁) (hs : s ∈ Ioc (0 : ℝ) S) {V : Fin n → ℝ}
    (hVq : ∀ i, V i ≤ (fwdMap W s q).re + W s)
    (hVW : ∀ i, V i ≠ W s) (hVinj : Function.Injective V) :
    ∃ ν M : ℝ, 0 < ν ∧ 0 < dd / 2 ∧ q + dd - p < 0 ∧
      Disjoint (ball ((q + dd - p : ℝ) : ℂ) (2 * (dd / 2)))
        (transl (-p) H₂ ∪ transl (-p) H₁) ∧
      (W 0 - p < q + dd - p) ∧
      (∀ i, V i - p < (fwdMap (fun u => W u - p) s ((q + dd - p : ℝ) : ℂ)).re + (W s - p)) ∧
      (∀ i, |V i - p| ≤ M) ∧
      (∀ i, ν ≤ |V i - p - (W s - p)|) ∧
      (∀ i j, i ≠ j → ν ≤ |V i - p - (V j - p)|) := by
  have hd := hpp.rad_pos
  obtain ⟨ν₁, hν₁, hν₁le⟩ := exists_pos_le_of_fintype (fun i => |V i - W s|)
    (fun i => abs_pos.2 (sub_ne_zero.2 (hVW i)))
  obtain ⟨ν₂, hν₂, hν₂le⟩ := exists_pos_le_of_fintype
    (fun ij : Fin n × Fin n => if ij.1 = ij.2 then 1 else |V ij.1 - V ij.2|) (fun ij => by
      by_cases hij : ij.1 = ij.2
      · simp only [hij, ↓reduceIte, one_pos]
      · simp only [hij, ↓reduceIte]
        exact abs_pos.2 (sub_ne_zero.2 fun he => hij (hVinj he)))
  have hqpd : q + dd < p := by
    have hpq := notMem_ball_of_mem_closure (hpp.prot.mono_right subset_union_right) hpp.src
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      not_lt, abs_of_pos (sub_pos.2 hpp.prot_lt)] at hpq
    linarith
  have hball : Disjoint (ball ((q + dd : ℝ) : ℂ) dd) (H₁ ∪ H₂) :=
    hpp.prot.mono_left fun z hz => by
      rw [mem_ball, dist_eq_norm] at hz ⊢
      calc
        ‖z - (q : ℂ)‖ = ‖(z - ((q + dd : ℝ) : ℂ)) + (dd : ℂ)‖ := by push_cast; ring_nf
        _ ≤ ‖z - ((q + dd : ℝ) : ℂ)‖ + ‖(dd : ℂ)‖ := norm_add_le _ _
        _ < dd + dd := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
          linarith
        _ = 2 * dd := by ring
  have hqH : Disjoint (ball ((q + dd - p : ℝ) : ℂ) (2 * (dd / 2)))
      (transl (-p) H₂ ∪ transl (-p) H₁) := by
    have h := disjoint_ball_transl hball (-p)
    rw [show 2 * (dd / 2) = dd by ring, show q + dd - p = q + dd + -p by ring]
    rw [transl, transl, ← Set.image_union, Set.union_comm]
    exact h
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (by rw [hW0]; exact hpp.prot_pos.ne') hS.le (by positivity)
    ((hpp.prot.mono_right subset_union_left).mono_right hK)
  obtain ⟨uqd, huqd⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (x := q + dd) (by rw [hW0]; linarith [hpp.prot_pos]) hS.le hd
    ((hball.mono_right subset_union_left).mono_right hK)
  have hlt := QuantumZipper.F1.isForwardSol_lt_of_lt hS.le
    (by linarith : q < q + dd) huq huqd s (Ioc_subset_Icc_self hs)
  refine ⟨min ν₁ ν₂, ∑ i, |V i - p|, lt_min hν₁ hν₂, by positivity,
    by linarith, hqH, by rw [hW0]; linarith [hpp.prot_pos], fun i => ?_,
    fun i => Finset.single_le_sum (fun j _ => abs_nonneg (V j - p)) (Finset.mem_univ i),
    fun i => ?_, fun i j hij => ?_⟩
  · rw [fwdMap_sub_const,
      show ((q + dd - p : ℝ) : ℂ) + (p : ℂ) = ((q + dd : ℝ) : ℂ) by push_cast; ring,
      fwdMap_eq_of_isForwardSol hW huqd (Ioc_subset_Icc_self hs)]
    rw [fwdMap_eq_of_isForwardSol hW huq (Ioc_subset_Icc_self hs)] at hVq
    linarith [hVq i]
  · simp only [sub_sub_sub_cancel_right]
    exact (min_le_left _ _).trans (hν₁le i)
  · simp only [sub_sub_sub_cancel_right]
    have h := hν₂le (i, j)
    simp only [hij, ↓reduceIte] at h
    exact (min_le_right _ _).trans h

end InteractingSLE.ZhanGT4.A1G3Lg
