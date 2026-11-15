/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformBound
import InteractingSLE.Spec.ZhanGT4.D9Const

/-!
# Bounds on seed coordinates from a bounded hull enclosure

Packet PROVE-ZHAN-GT4-A22. The alive real points at the two ends of a
larger disc bracket every integrated seed coordinate. Their mapping-out
images have the existing enclosure bound.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap fwdHull)

/-- A seed coordinate cannot leave the real bounds supplied by a hull disc. -/
theorem IsSeedCoordinate.abs_le_of_hull_subset_ball {W V : ℝ → ℝ} {T R : ℝ}
    (h : IsSeedCoordinate W V T) (hW : Continuous W) (hT : 0 ≤ T) (hR : 0 < R)
    (hK : fwdHull W T ⊆ closedBall (0 : ℂ) R) (hW0 : |W 0| ≤ R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : |V t| ≤ 7 * R := by
  have hfar : ∀ y : ℝ, |y| = 2 * R →
      Disjoint (ball (y : ℂ) R) (fwdHull W T) := by
    intro y hy
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have h1 := hK hzK
    rw [mem_closedBall_zero_iff] at h1
    rw [mem_ball, dist_eq_norm] at hz
    have h2 : ‖(y : ℂ)‖ ≤ ‖z‖ + ‖z - y‖ := by
      calc ‖(y : ℂ)‖ = ‖z - (z - y)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖z - y‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs, hy] at h2
    linarith
  have hW0' := abs_le.1 hW0
  obtain ⟨ur, hur⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (show 2 * R ≠ W 0 by intro he; linarith) hT hR
    (hfar (2 * R) (abs_of_pos (by positivity)))
  obtain ⟨ul, hul⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (show -(2 * R) ≠ W 0 by intro he; linarith) hT hR
    (hfar (-(2 * R)) (by rw [abs_neg, abs_of_pos (by positivity)]))
  have hright := h.lt_gmap hW (by linarith : W 0 < 2 * R) hur ht
  have hleft := h.gmap_lt hW (by linarith : -(2 * R) < W 0) hul ht
  have hKt := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hK
  have hbr := norm_sol_add_sub_le hW ht.1 hR hKt (isForwardSol_restrict hur ht.2)
  have hbl := norm_sol_add_sub_le hW ht.1 hR hKt (isForwardSol_restrict hul ht.2)
  have hrre := (Complex.abs_re_le_norm _).trans hbr
  have hlre := (Complex.abs_re_le_norm _).trans hbl
  simp only [Complex.ofReal_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos (show 0 < 2 * R by positivity), Complex.add_re, Complex.ofReal_re] at hrre hlre
  rw [abs_le] at hrre hlre ⊢
  constructor <;> linarith

/-- The same bound holds throughout the interval between two seed coordinates. -/
theorem abs_le_of_mem_seed_interval {W Vlo Vhi : ℝ → ℝ} {T R t x : ℝ}
    (hlo : IsSeedCoordinate W Vlo T) (hhi : IsSeedCoordinate W Vhi T)
    (hW : Continuous W) (hT : 0 ≤ T) (hR : 0 < R)
    (hK : fwdHull W T ⊆ closedBall (0 : ℂ) R) (hW0 : |W 0| ≤ R)
    (ht : t ∈ Icc (0 : ℝ) T) (hx : x ∈ uIcc (Vlo t) (Vhi t)) : |x| ≤ 7 * R := by
  have hl := abs_le.1 (hlo.abs_le_of_hull_subset_ball hW hT hR hK hW0 ht)
  have hh := abs_le.1 (hhi.abs_le_of_hull_subset_ball hW hT hR hK hW0 ht)
  exact abs_le.2 ⟨(le_min hl.1 hh.1).trans hx.1, hx.2.trans (max_le hl.2 hh.2)⟩

/-- Two fixed protected real points retain a uniform positive separation,
and the derivative at the right point has a uniform positive lower bound. -/
theorem exists_protected_pair_gap {H₁ : Set ℂ} (hH₁ : IsHPHull H₁)
    {q p ρq ρp : ℝ} (hρq : 0 < ρq) (hρp : 0 < ρp)
    (hqH : Disjoint (ball (q : ℂ) ρq) H₁)
    (hpH : Disjoint (ball (p : ℂ) ρp) H₁) (hq : 0 < q) (hqp : q < p) (Tm : ℝ) :
    ∃ μ c : ℝ, 0 < μ ∧ 0 < c ∧
      ∀ (W : ℝ → ℝ) (T : ℝ), Continuous W → W 0 = 0 → 0 ≤ T → T ≤ Tm →
        ((W 0 : ℝ) : ℂ) ∈ closure H₁ → fwdHull W T ⊆ H₁ →
        ∃ uq up : ℝ → ℂ, IsForwardSol W (q : ℂ) T uq ∧ IsForwardSol W (p : ℂ) T up ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            μ ≤ (deriv (fwdMap W t) p).re ∧ (deriv (fwdMap W t) p).re ≤ 1) ∧
          (∀ t ∈ Icc (0 : ℝ) T, c ≤ (up t).re - (uq t).re) := by
  obtain ⟨μq, hμq, hderq⟩ := exists_deriv_fwdMap_real_bounds hH₁ hρq hqH
  obtain ⟨μp, hμp, hderp⟩ := exists_deriv_fwdMap_real_bounds hH₁ hρp hpH
  let β := ρq / 96 * μq
  have hβ : 0 < β := by dsimp only [β]; positivity
  let c := (p - q) * Real.exp (-(2 / β ^ 2 * |Tm|))
  refine ⟨μp, c, hμp, mul_pos (sub_pos.2 hqp) (Real.exp_pos _), ?_⟩
  intro W T hW hW0 hT hTm hW0H hK
  have hnotq := notMem_ball_of_mem_closure hqH hW0H
  have hnotp := notMem_ball_of_mem_closure hpH hW0H
  have hnq : ∀ y : ℝ, (y : ℂ) ∈ ball (q : ℂ) (ρq / 2) → y ≠ W 0 := by
    intro y hy he
    apply hnotq
    rw [← he]
    exact ball_subset_ball (by linarith) hy
  have hnp : ∀ y : ℝ, (y : ℂ) ∈ ball (p : ℂ) (ρp / 2) → y ≠ W 0 := by
    intro y hy he
    apply hnotp
    rw [← he]
    exact ball_subset_ball (by linarith) hy
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (by rw [hW0]; exact hq.ne') hT hρq (hqH.mono_right hK)
  obtain ⟨up, hup⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (by rw [hW0]; exact (hq.trans hqp).ne') hT hρp (hpH.mono_right hK)
  have hgapq : ∀ t ∈ Icc (0 : ℝ) T, β ≤ ‖uq t‖ := by
    intro t ht
    have hKt := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hK
    have hμ := (hderq W hW t ht.1 hKt hnq).2.1
    have hk := le_norm_fwdMap_real hW ht.1 hρq (hqH.mono_right hKt) hnq
    rw [fwdMap_eq_of_isForwardSol hW huq ht] at hk
    exact (mul_le_mul_of_nonneg_left (hμ.trans (Complex.re_le_norm _))
      (by positivity : 0 ≤ ρq / 96)).trans hk
  have hqpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < (uq t).re := by
    intro t ht
    exact QuantumZipper.re_pos_isForwardSol_real hW hT huq (by rwa [hW0]) t ht
  have hord := QuantumZipper.F1.isForwardSol_lt_of_lt hT hqp huq hup
  have hgap : ∀ t ∈ Icc (0 : ℝ) T, β ≤ ‖up t‖ := by
    intro t ht
    have hqi := im_eq_zero_of_isForwardSol_real hW huq ht
    have hbq := hgapq t ht
    rw [← abs_re_eq_norm.2 hqi, abs_of_pos (hqpos t ht)] at hbq
    exact hbq.trans ((hord t ht).le.trans (Complex.re_le_norm _))
  refine ⟨uq, up, huq, hup, ?_, ?_⟩
  · intro t ht
    exact (hderp W hW t ht.1 (((QuantumZipper.fwdHull_mono).1 ht.2).trans hK) hnp).2
  · intro t ht
    have hb := (norm_sol_sub_bounds huq hup hβ hgapq hgap ht).1
    have hi : ‖(p : ℂ) - q‖ = p - q := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.2 hqp)]
    have he : up t - uq t = (((up t).re - (uq t).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [im_eq_zero_of_isForwardSol_real hW hup ht, im_eq_zero_of_isForwardSol_real hW huq ht]
    rw [hi, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.2 (hord t ht))] at hb
    apply le_trans ?_ hb
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (sub_pos.2 hqp).le
    exact neg_le_neg (mul_le_mul_of_nonneg_left
      ((ht.2.trans hTm).trans (le_abs_self Tm)) (by positivity))

end InteractingSLE.ZhanGT4
