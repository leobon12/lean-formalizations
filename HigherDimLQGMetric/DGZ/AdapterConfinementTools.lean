import HigherDimLQGMetric.DGZ.AdapterNondeg
import HigherDimLQGMetric.DGZ.FunctionalsBounds

/-! Geometry and diameter facts for the confinement clause of the real-cutoff adapter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-- The scaled Euclidean sphere-to-sphere distance dominates a hypercubic crossing.
The outer Euclidean radius is chosen with a strict `√d` margin. -/
theorem adapter_sphere_distance_ge_cross {φ : Rd d → ℝ} {ξ r R' s : ℝ}
    (hd : 0 < d) (hφ : Continuous φ) (hr : 0 < r) (hR' : 2 * r < R')
    (hs : 1 / 2 < s) (hs1 : s ≤ 1) :
    s * acrossDist ξ (fun z => φ (s • z)) 0 R' (2 * r) ≤
      lfppSetDist ξ φ univ (Metric.sphere (0 : Rd d) r)
        (Metric.sphere (0 : Rd d) ((Real.sqrt d + 1) * R')) := by
  have hs0 : 0 < s := by linarith
  have hR'0 : 0 < R' := by linarith
  let R : ℝ := (Real.sqrt d + 1) * R'
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hsphere (t : ℝ) (ht : 0 ≤ t) : (Metric.sphere (0 : Rd d) t).Nonempty := by
    refine ⟨t • e₁ d, ?_⟩
    change dist (t • e₁ d) 0 = t
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
      norm_e₁ hd, mul_one]
  have hXc : Continuous (fun z => φ (s • z)) :=
    hφ.comp (continuous_id.const_smul s)
  apply le_lfppSetDist (hsphere r hr.le) (hsphere R hR0.le)
  intro x hx y hy
  have hp : s⁻¹ • x ∈ cbox (0 : Rd d) (2 * r) := by
    have hxnorm : ‖x‖ = r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    have hsi : s⁻¹ ≤ 2 := by
      rw [← one_div]
      exact (div_le_iff₀ hs0).2 (by linarith)
    have hn : ‖s⁻¹ • x‖ ≤ 2 * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0), hxnorm]
      exact mul_le_mul_of_nonneg_right hsi hr.le
    intro i
    simpa only [PiLp.zero_apply, sub_zero] using
      (HigherDimLFPP.DGZ.abs_apply_le_norm (s⁻¹ • x) i).trans hn
  have hq : s⁻¹ • y ∉ obox (0 : Rd d) R' := by
    intro hq
    have hsmall : ‖s⁻¹ • y‖ ≤ Real.sqrt d * R' := by
      simpa only [zero_sub, norm_neg] using (tn_norm_sub_le hq)
    have hyNorm : ‖y‖ = R := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hy
    have hsi : 1 ≤ s⁻¹ := by simpa only [one_div] using (one_le_div hs0).2 hs1
    have hlarge : R ≤ ‖s⁻¹ • y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0), hyNorm]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsi hR0.le
    have hstrict : Real.sqrt d * R' < R := by
      dsimp [R]
      nlinarith [hR'0]
    linarith
  have hcross := acrossDist_le_lfppMetric_of_mem (ξ := ξ) hXc hR' hp hq
  have hscale : lfppMetric ξ φ x y =
      s * lfppMetric ξ (fun z => φ (s • z)) (s⁻¹ • x) (s⁻¹ • y) := by
    have hh := lfppMetric_sim (LinearIsometryEquiv.refl ℝ (Rd d)) 0 ξ
      φ hs0 (s⁻¹ • x) (s⁻¹ • y)
    simpa only [zero_add, LinearIsometryEquiv.coe_refl, id, smul_smul,
      mul_inv_cancel₀ hs0.ne', one_smul] using hh
  change s * acrossDist ξ (fun z => φ (s • z)) 0 R' (2 * r) ≤ lfppMetric ξ φ x y
  rw [hscale]
  exact mul_le_mul_of_nonneg_left hcross hs0.le

/-- A Hölder bound on a closed ball controls the supremum of all distances on its open ball. -/
theorem adapter_ball_diam_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {G : ℝ → Rd d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    {ξ ε β r M C : ℝ} {N : ℕ} (hβ : 0 ≤ β) (hr : 0 < r)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (haQ : 0 ≤ aQ P H ξ N 2⁻¹)
    (hmed : aHat P G ξ ε ≤ C * aQ P H ξ N 2⁻¹)
    (ω : Ω)
    (hholder : ∀ x ∈ Metric.closedBall (0 : Rd d) r,
      ∀ y ∈ Metric.closedBall (0 : Rd d) r,
        lfppMetric ξ (fun z => G ε z ω) x y ≤
          M * aHat P G ξ ε * ‖x - y‖ ^ β) :
    (⨆ p : Metric.ball (0 : Rd d) r × Metric.ball (0 : Rd d) r,
      lfppMetric ξ (fun z => G ε z ω) p.1 p.2) ≤
      (M * C * (2 * r) ^ β) * aQ P H ξ N 2⁻¹ := by
  have hzero : (0 : Rd d) ∈ Metric.ball (0 : Rd d) r := by
    simpa only [Metric.mem_ball, dist_self] using hr
  have hne : Nonempty (Metric.ball (0 : Rd d) r × Metric.ball (0 : Rd d) r) :=
    ⟨(⟨0, hzero⟩, ⟨0, hzero⟩)⟩
  apply @ciSup_le ℝ _ _ hne
  intro p
  have hx : (p.1 : Rd d) ∈ Metric.closedBall (0 : Rd d) r :=
    Metric.ball_subset_closedBall p.1.property
  have hy : (p.2 : Rd d) ∈ Metric.closedBall (0 : Rd d) r :=
    Metric.ball_subset_closedBall p.2.property
  have hxn : ‖(p.1 : Rd d)‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hyn : ‖(p.2 : Rd d)‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hnorm : ‖(p.1 : Rd d) - p.2‖ ≤ 2 * r := by
    calc
      _ ≤ ‖(p.1 : Rd d)‖ + ‖(p.2 : Rd d)‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  have hpow : ‖(p.1 : Rd d) - p.2‖ ^ β ≤ (2 * r) ^ β :=
    Real.rpow_le_rpow (norm_nonneg _) hnorm hβ
  calc
    lfppMetric ξ (fun z => G ε z ω) p.1 p.2
        ≤ M * aHat P G ξ ε * ‖(p.1 : Rd d) - p.2‖ ^ β :=
          hholder p.1 hx p.2 hy
    _ ≤ M * (C * aQ P H ξ N 2⁻¹) * ‖(p.1 : Rd d) - p.2‖ ^ β := by
          gcongr
    _ ≤ M * (C * aQ P H ξ N 2⁻¹) * (2 * r) ^ β := by
          gcongr
    _ = (M * C * (2 * r) ^ β) * aQ P H ξ N 2⁻¹ := by ring

end HigherDimLQGMetric.DGZ
