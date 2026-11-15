/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstSource

/-!
# Uniform bounds for finitely many actual boundary accesses

Packet PROVE-ZHAN-GT4-A22. The accesses may be integrated seed coordinates
in a frozen chart. A single image enclosure gives all their force gaps and
boundary derivative scales before the opposite path and horizon are chosen.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)

/-- Finite clear accesses have uniform alive flows, driver gaps and
boundary derivative scales over every chain inside one hull enclosure. -/
theorem exists_access_bounds_of_enclosure {ι : Type*} [Fintype ι] {E : Set ℂ}
    (hE : IsHPHull E) (ζ : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ i, Disjoint (ball (ζ i : ℂ) ρ) E) :
    ∃ c C L : ℝ, 0 < c ∧ 0 ≤ C ∧ 0 ≤ L ∧ ∀ (W : ℝ → ℝ) (T : ℝ),
      Continuous W → 0 ≤ T → ((W 0 : ℝ) : ℂ) ∈ closure E → fwdHull W T ⊆ E →
      ∀ i, (∃ q, IsForwardSol W ((ζ i : ℝ) : ℂ) T q) ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          c ≤ |(fwdMap W t (ζ i)).re| ∧ |(fwdMap W t (ζ i)).re| ≤ C ∧
            InScale L (deriv (fwdMap W t) (ζ i)).re := by
  choose ci Ci hci hCi hbi using fun i => exists_source_gap_bounds_of_enclosure hE hρ (hc i)
  choose μ hμ hdi using fun i => exists_deriv_fwdMap_real_bounds hE hρ (hc i)
  obtain ⟨c, hcp, hcle⟩ := exists_pos_le_of_fintype ci hci
  obtain ⟨m, hmp, hmle⟩ := exists_pos_le_of_fintype μ hμ
  obtain ⟨L, hL, hscale⟩ := exists_inScale_of_abs_bounds hmp (by norm_num : (0 : ℝ) < 1)
  refine ⟨c, (∑ i, Ci i) + 1, L, hcp,
    add_nonneg (Finset.sum_nonneg fun i _ => hCi i) zero_le_one, hL, ?_⟩
  intro W T hW hT hsrc hK i
  obtain ⟨hq, hb⟩ := hbi i W T hW hT hsrc hK
  refine ⟨hq, fun t ht => ?_⟩
  have hBt := hb t ht
  have hnorm : ∀ y : ℝ, (y : ℂ) ∈ ball (ζ i : ℂ) (ρ / 2) → y ≠ W 0 := by
    intro y hy he
    apply notMem_ball_of_mem_closure (hc i) hsrc
    rw [← he]
    exact ball_subset_ball (by linarith) hy
  have hKt := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hK
  have hd := hdi i W hW t ht.1 hKt hnorm
  have hpos := (hmle i).trans hd.2.1
  refine ⟨(hcle i).trans hBt.1, ?_, hscale _ ?_ ?_⟩
  · exact hBt.2.trans ((Finset.single_le_sum (fun j _ => hCi j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right zero_le_one))
  · simpa only [abs_of_pos (hmp.trans_le hpos)] using hpos
  · simpa only [abs_of_pos (hmp.trans_le hpos)] using hd.2.2

/-- Distinct real image accesses retain their initial separation, up to
one uniform exponential factor, under a common positive driver-gap bound. -/
theorem OwnData.frzImg_sub_bounds_of_gap {W U a : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ}
    {T t Tm c x y : ℝ} (h : OwnData W A φ T a U)
    {vx vy : ℝ → ℂ} (hx : IsForwardSol U (x : ℂ) (a T) vx)
    (hy : IsForwardSol U (y : ℂ) (a T) vy) (hc : 0 < c)
    (hcx : ∀ u ∈ Icc (0 : ℝ) T, c ≤ |(fwdMap U (a u) x).re|)
    (hcy : ∀ u ∈ Icc (0 : ℝ) T, c ≤ |(fwdMap U (a u) y).re|)
    (hclock : a t ≤ Tm) (ht : t ∈ Icc (0 : ℝ) T) :
    |y - x| * Real.exp (-(2 / c ^ 2 * Tm)) ≤ |frzImg U a y t - frzImg U a x t| := by
  have hb := (h.toImgData.norm_fwdMap_sub_bounds hx hy hc
    (fun u hu => (hcx u hu).trans (Complex.abs_re_le_norm _))
    (fun u hu => (hcy u hu).trans (Complex.abs_re_le_norm _)) ht).1
  have him : (fwdMap U (a t) y - fwdMap U (a t) x).im = 0 := by
    rw [sub_im, fwdMap_real_im h.contW' hy (h.mapsTo_clock ht),
      fwdMap_real_im h.contW' hx (h.mapsTo_clock ht), sub_self]
  rw [← abs_re_eq_norm.2 him, sub_re] at hb
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb
  have hgap : (fwdMap U (a t) y).re - (fwdMap U (a t) x).re =
      frzImg U a y t - frzImg U a x t := by unfold frzImg; ring
  rw [hgap] at hb
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
    (neg_le_neg (mul_le_mul_of_nonneg_left hclock (by positivity)))) (abs_nonneg _)).trans hb

end InteractingSLE.ZhanGT4
