import HigherDimLQGMetric.LfppTight.PureClosureMetric
import HigherDimLQGMetric.LfppTight.CrossMain

/-! Deterministic passage from a ratio crossing to an absolute outer distance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l6a_cross_point_lower_inf {d : ℕ}
    (D : Rd d × Rd d → ℝ) (s R C δ : ℝ)
    (hC : 0 < C)
    (h0 : (0 : Rd d) ∈ ball 0 s) (he : e₁ d ∈ ball (0 : Rd d) s)
    (hpoint : δ ≤ D (0, e₁ d))
    (hcross : supPairs D (ball (0 : Rd d) s) ≤
      ENNReal.ofReal C⁻¹ * infPairs D (sphere 0 s) (sphere 0 (R * s))) :
    ENNReal.ofReal (C * δ) ≤
      infPairs D (sphere (0 : Rd d) s) (sphere 0 (R * s)) := by
  have hsup : ENNReal.ofReal δ ≤ supPairs D (ball (0 : Rd d) s) := by
    unfold supPairs
    exact le_iSup_of_le 0 (le_iSup_of_le h0
      (le_iSup_of_le (e₁ d) (le_iSup_of_le he
        (ENNReal.ofReal_le_ofReal hpoint))))
  have hmul := mul_le_mul_of_nonneg_left (hsup.trans hcross)
    (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal C)
  calc
    ENNReal.ofReal (C * δ) = ENNReal.ofReal C * ENNReal.ofReal δ :=
      ENNReal.ofReal_mul hC.le
    _ ≤ ENNReal.ofReal C *
        (ENNReal.ofReal C⁻¹ * infPairs D (sphere 0 s) (sphere 0 (R * s))) := hmul
    _ = infPairs D (sphere 0 s) (sphere 0 (R * s)) := by
      rw [ENNReal.ofReal_inv_of_pos hC, ← mul_assoc,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hC).ne'
          ENNReal.ofReal_ne_top, one_mul]

theorem l6a_cross_norm_iff_raw_general {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) (v : DistRd d)
    (hfield : Continuous fun z => convMollify κ ε v z)
    (A B C : Set (Rd d)) (c : ℝ) :
    (supPairs (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v)) A ≤
      ENNReal.ofReal c * infPairs
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v)) B C) ↔
    (supPairs (lfppDist κ ξ ε v) A ≤
      ENNReal.ofReal c * infPairs (lfppDist κ ξ ε v) B C) := by
  have ha : 0 < (aEps κ ξ ε)⁻¹ :=
    inv_pos.mpr (l6a_aEps_pos hd κ hκ ξ hε)
  have hdist : Continuous (lfppDist κ ξ ε v) := by
    change Continuous (fun p : Rd d × Rd d =>
      DGZ.lfppMetric ξ (convMollify κ ε v) p.1 p.2)
    exact DGZ.continuous_lfppMetric hfield ξ
  have heq : toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v) =
      (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v := by
    apply funext
    intro q
    rw [toCMapRd_apply_of_continuous (hdist.const_smul _)]
  rw [heq]
  have hsmul : ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε v) =
      fun p => (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε v p := rfl
  rw [hsmul]
  exact l6a_cross_iff_mul (lfppDist κ ξ ε v) A B C ha

theorem l6a_le_nd_setInf_of_pair_lower {d : ℕ}
    (A B : Set (Rd d)) (hA : A.Nonempty) (hB : B.Nonempty)
    (D : C(Rd d × Rd d, ℝ)) (M : ℝ)
    (h : ∀ x ∈ A, ∀ y ∈ B, M ≤ D (x, y)) :
    M ≤ DGZ.nd_setInf A B D := by
  unfold DGZ.nd_setInf DGZ.nd_pairInf
  exact le_csInf ((hA.prod hB).image D)
    (by rintro _ ⟨p, hp, rfl⟩; exact h p.1 hp.1 p.2 hp.2)

theorem l6a_nd_setInf_le_pair {d : ℕ}
    (A B : Set (Rd d)) (hA : IsCompact A) (hB : IsCompact B)
    (D : C(Rd d × Rd d, ℝ)) {x y : Rd d}
    (hx : x ∈ A) (hy : y ∈ B) :
    DGZ.nd_setInf A B D ≤ D (x, y) :=
  DGZ.nd_pairInf_le (hA.prod hB) D ⟨hx, hy⟩

theorem l6a_cross_sep_implies_far {d : ℕ} (hd : 0 < d)
    (ξ a : ℝ) (ha : 0 < a) (φ : Rd d → ℝ) (hφ : Continuous φ)
    (n k : ℕ) {s R C : ℝ} (hs : (n : ℝ) + 1 < s)
    (hR : 1 < R) (hC : 0 < C)
    (hCn : (n : ℝ) ≤ C * (1 / ((k : ℝ) + 1)))
    (hsep : DGZ.normMetricC ξ φ a ∈ metricSepSet_select 0 0 k)
    (hcross : supPairs (DGZ.normMetricC ξ φ a) (ball (0 : Rd d) s) ≤
      ENNReal.ofReal C⁻¹ * infPairs (DGZ.normMetricC ξ φ a)
        (sphere 0 s) (sphere 0 (R * s))) :
    (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n)
      (sphere 0 (R * s)) (DGZ.normMetricC ξ φ a) := by
  let D := DGZ.normMetricC ξ φ a
  let δ : ℝ := 1 / ((k : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hs0 : 0 < s := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hRpos : 0 < R * s := mul_pos (by linarith) hs0
  have h0 : (0 : Rd d) ∈ ball 0 s := mem_ball_self hs0
  have he : e₁ d ∈ ball (0 : Rd d) s := by
    rw [mem_ball, dist_zero_right, HigherDimLFPP.norm_e₁ hd]
    linarith
  have hpoint : δ ≤ D (0, e₁ d) := by
    have h0c : (0 : Rd d) ∈ closedBall 0 (0 : ℕ) := by simp
    have h1 : (1 : ℝ) ≤ ‖e₁ d - (0 : Rd d)‖ := by
      rw [sub_zero, HigherDimLFPP.norm_e₁ hd]
    exact hsep 0 h0c (e₁ d) (by simpa only [Nat.cast_zero, zero_add, div_one] using h1)
  have hshellE : ENNReal.ofReal (C * δ) ≤
      infPairs D (sphere (0 : Rd d) s) (sphere 0 (R * s)) :=
    l6a_cross_point_lower_inf D s R C δ hC h0 he hpoint hcross
  have hshell : (n : ℝ) ≤
      DGZ.nd_setInf (sphere (0 : Rd d) s) (sphere 0 (R * s)) D := by
    apply l6a_le_nd_setInf_of_pair_lower _ _
      (l6a_sphere_nonempty hd 0 hs0.le)
      (l6a_sphere_nonempty hd 0 hRpos.le) D n
    intro u hu v hv
    have hpointE : infPairs D (sphere (0 : Rd d) s)
        (sphere 0 (R * s)) ≤ ENNReal.ofReal (D (u, v)) := by
      unfold infPairs
      exact iInf_le_of_le u (iInf_le_of_le hu
        (iInf_le_of_le v (iInf_le _ hv)))
    have hnonneg : 0 ≤ D (u, v) := by
      rw [DGZ.normMetricC_apply hφ]
      exact mul_nonneg (inv_pos.mpr ha).le (DGZ.lfppMetric_nonneg ξ φ u v)
    have hreal : C * δ ≤ D (u, v) :=
      (ENNReal.ofReal_le_ofReal_iff hnonneg).1 (hshellE.trans hpointE)
    exact hCn.trans hreal
  have hpair : ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ y ∈ sphere 0 (R * s), (n : ℝ) ≤ D (x, y) := by
    intro x hx y hy
    have hxS : x ∈ closedBall (0 : Rd d) s :=
      (closedBall_subset_closedBall (by linarith : (n : ℝ) ≤ s)) hx
    have hyS : y ∉ ball (0 : Rd d) (R * s) := by
      rw [mem_sphere] at hy
      intro hh
      exact (not_lt_of_ge hy.ge) (mem_ball.mp hh)
    exact hshell.trans (l6a_normMetric_shell_barrier ξ a φ hφ ha 0
      (by nlinarith : s < R * s) hxS hyS)
  exact l6a_le_nd_setInf_of_pair_lower _ _
    ⟨0, mem_closedBall_self (by exact_mod_cast Nat.zero_le n)⟩
    (l6a_sphere_nonempty hd 0 hRpos.le) D n hpair

theorem l6a_proper_of_real_setInf {d : ℕ} (D : C(Rd d × Rd d, ℝ))
    (h : ∀ n : ℕ, ∃ R : ℝ, (n : ℝ) < R ∧
      (n : ℝ) ≤ DGZ.nd_setInf (closedBall (0 : Rd d) n) (sphere 0 R) D) :
    IsProperFn D := by
  intro r hr M
  obtain ⟨n, hn⟩ := exists_nat_gt (max r M)
  obtain ⟨R, hR, hbound⟩ := h n
  refine ⟨R, (lt_of_le_of_lt (le_max_left _ _) hn).trans hR, ?_⟩
  have hrn : r ≤ (n : ℝ) := (le_max_left _ _).trans hn.le
  have hMn : M ≤ (n : ℝ) := (le_max_right _ _).trans hn.le
  unfold infPairs
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  have hx' : x ∈ closedBall (0 : Rd d) n := by
    exact (closedBall_subset_closedBall hrn) hx
  have hxy := l6a_nd_setInf_le_pair (closedBall (0 : Rd d) n) (sphere 0 R)
    (isCompact_closedBall _ _) (isCompact_sphere _ _) D hx' hy
  exact ENNReal.ofReal_le_ofReal (hMn.trans (hbound.trans hxy))

end HigherDimLQGMetric
