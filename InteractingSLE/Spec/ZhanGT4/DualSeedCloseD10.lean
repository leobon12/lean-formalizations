/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseForce
import InteractingSLE.Spec.ZhanGT4.DualSeedLawPath

/-!
# The seeded D10 drift in capacity coordinates

Packet PROVE-ZHAN-GT4-A22. Include the other tip as the first force, with
charge `-κ/2`. The remaining charges are `κ r_m`. Capacity substitution
transports each entrance integral, then the finite sum defining D10.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4
namespace SeedData

/-- The other tip and original seed charges in one finite force word. -/
def imageCharge {n : ℕ} (s : SeedData n) : Fin (n + 1) → ℝ :=
  Fin.cases (-(s.κ / 2)) (fun m => s.κ * s.r m)

/-- The corresponding own-time image force coordinates. -/
def imageForce {n : ℕ} (s : SeedData n) (t : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases (s.A20 t) (s.B0 t)

/-- The D10 rate is exactly the sum of the image force drifts, multiplied
by the capacity rate. This identity also holds at a zero seed gap. -/
theorem d10Rate_eq_imageCharge {n : ℕ} (s : SeedData n) (t : ℝ) :
    s.d10Rate t = ∑ i, s.A 1 t ^ 2 *
      (s.imageCharge i / (s.A 0 t - s.imageForce t i)) := by
  rw [← Finset.mul_sum, Fin.sum_univ_succ]
  simp only [imageCharge, imageForce, Fin.cases_zero, Fin.cases_succ]
  unfold d10Rate
  congr 1
  rw [div_mul_eq_div_div]
  ring

/-- Entrance integrability for every weighted image gap. Seeds use the
checked entrance estimate; the other tip uses its protected nonzero gap. -/
theorem imageWeightedGap_integrable {n : ℕ} (s : SeedData n) {A : Set ℂ} {T : ℝ}
    (h : OwnData s.W A s.φ T s.a s.W')
    (hc : ContinuousOn s.A20 (Icc 0 T))
    (hne : ∀ t ∈ Icc (0 : ℝ) T, s.A 0 t ≠ s.A20 t)
    (hi : s.ImageEntranceIntegrable T) (i : Fin (n + 1)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun u => s.A 1 u ^ 2 / (s.A 0 u - s.imageForce u i)) volume 0 t := by
  refine Fin.cases ?_ (fun m => ?_) i
  · have hh : ContinuousOn (fun u => s.A 1 u ^ 2 / (s.A 0 u - s.A20 u)) (Icc 0 T) :=
      ((h.continuousOn_frzA 1).pow 2).div ((h.continuousOn_frzA 0).sub hc)
        (fun u hu => sub_ne_zero.2 (hne u hu))
    exact (hh.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  · apply ((hi m t ht).const_mul (-(1 / 2) : ℝ)).congr
    intro u _
    dsimp only [imageForce, Fin.cases_succ]
    rw [show s.B0 u m - s.A 0 u = -(s.A 0 u - s.B0 u m) by ring, div_neg]
    ring

/-- Capacity substitution for the complete D10 sum. The coordinate
identities allow any common translation `c` of driver and forces. -/
theorem integral_d10_capacity {n : ℕ} (s : SeedData n) {A : Set ℂ} {T c t : ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') (ht : t ∈ Icc (0 : ℝ) T)
    {w : ℝ → ℝ} {v : Fin (n + 1) → ℝ → ℝ}
    (hw : ∀ u ∈ Icc (0 : ℝ) T, w (s.a u) = s.A 0 u - c)
    (hv : ∀ i u, u ∈ Icc (0 : ℝ) T → v i (s.a u) = s.imageForce u i - c)
    (hi : ∀ i, IntervalIntegrable
      (fun u => s.A 1 u ^ 2 / (s.A 0 u - s.imageForce u i)) volume 0 t) :
    (∀ i, IntervalIntegrable (fun u => s.imageCharge i / (w u - v i u)) volume 0 (s.a t)) ∧
      (∫ u in (0 : ℝ)..t, s.d10Rate u) =
        ∑ i, ∫ u in (0 : ℝ)..s.a t, s.imageCharge i / (w u - v i u) := by
  have he (i : Fin (n + 1)) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) t) :
      s.imageCharge i * (s.A 1 u ^ 2 / (s.A 0 u - s.imageForce u i)) =
        s.A 1 u ^ 2 * (s.imageCharge i / (w (s.a u) - v i (s.a u))) := by
    rw [hw u ⟨hu.1, hu.2.trans ht.2⟩, hv i u ⟨hu.1, hu.2.trans ht.2⟩]
    rw [sub_sub_sub_cancel_right]
    ring
  have hii (i : Fin (n + 1)) : IntervalIntegrable (fun u =>
      s.A 1 u ^ 2 * (s.imageCharge i / (w (s.a u) - v i (s.a u)))) volume 0 t := by
    apply ((hi i).const_mul (s.imageCharge i)).congr
    intro u hu
    rw [uIoc_of_le ht.1] at hu
    exact he i u ⟨hu.1.le, hu.2⟩
  refine ⟨fun i => (h.intervalIntegrable_capacity_iff _ ht).1 (hii i), ?_⟩
  have hiown (i : Fin (n + 1)) : IntervalIntegrable (fun u =>
      s.A 1 u ^ 2 * (s.imageCharge i / (s.A 0 u - s.imageForce u i))) volume 0 t := by
    convert (hi i).const_mul (s.imageCharge i) using 1
    funext u
    ring
  simp_rw [s.d10Rate_eq_imageCharge]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hiown i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← h.integral_capacity_substitution (fun u => s.imageCharge i / (w u - v i u)) ht]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht.1] at hu
  dsimp only
  rw [hw u ⟨hu.1, hu.2.trans ht.2⟩, hv i u ⟨hu.1, hu.2.trans ht.2⟩,
    sub_sub_sub_cancel_right]
  rfl

end SeedData
end InteractingSLE.ZhanGT4
