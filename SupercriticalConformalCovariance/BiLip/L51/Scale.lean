import SupercriticalConformalCovariance.BiLip.L51.Transfer
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EScale

/-!
# Lemma 5.1: homogeneity of the literal good event

`good_scale_iff`: multiplying the source metric and the target function by `λ = e^{ξ t}` and shifting the
circle-average value by `t` leaves `SupercriticalConformalCovariance.Improve.Good` (G1–G5) unchanged. Every clause is homogeneous of degree
one, and `m_{z,r} = r^{ξQ} e^{ξ c}` carries the same factor. This is the pattern of S36 `attained_scale_iff`,
plus the internal barrier, `aroundRat`, point-to-circle costs and the regular pairs of (7)–(8).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.L51

open SupercriticalLQGUniqueness (LSCMetric EuclideanAnnulus aroundDist acrossDist)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events (eventCarrier eventMiddle eventBoundary
  pointSphereDist spherePairInf)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36 (ibg_scale_iff scale_le_scale_iff scale_le_iff
  mul_lt_top_iff_of_ne ofReal_N_shift E4Prop)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated (aroundRat)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (Geodesic)
open SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses (isCurve_iff_of_dist_scale
  len_eq_mul_of_dist_scale internal_eq_mul_of_dist_scale aroundDist_eq_mul_of_dist_scale
  acrossDist_eq_mul_of_dist_scale)

section Scaling

variable {d₁ d₂ : LSCMetric} {k : ℝ≥0∞}

theorem spherePairInf_scale (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y))
    (c : ℂ) (ρ σ : ℝ) : spherePairInf d₂ c ρ σ = k * spherePairInf d₁ c ρ σ := by
  unfold spherePairInf
  simp only [hd, ENNReal.mul_iInf_of_ne hk0 hkt]

theorem pointSphereDist_scale (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y))
    (x : ℂ) (ρ : ℝ) : pointSphereDist d₂ x ρ = k * pointSphereDist d₁ x ρ :=
  spherePairInf_scale hk0 hkt hd x 0 ρ

theorem aroundRat_scale (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y))
    (p : ℂ × ℝ × ℝ) : aroundRat (d₂, p) = k * aroundRat (d₁, p) := by
  unfold aroundRat
  simp only [aroundDist_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hd, ENNReal.mul_iInf_of_ne hk0 hkt]

theorem barrier_scale (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y))
    (z : ℂ) (r : Ioi (0 : ℝ)) :
    SupercriticalConformalCovariance.GoodAnnulus.barrier d₂ z r = k * SupercriticalConformalCovariance.GoodAnnulus.barrier d₁ z r := by
  unfold SupercriticalConformalCovariance.GoodAnnulus.barrier LSCMetric.internalSetDist
  simp only [internal_eq_mul_of_dist_scale d₁ d₂ k hk0 hkt hd, ENNReal.mul_iInf_of_ne hk0 hkt]

theorem geodesic_scale_iff (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y))
    (P : ℝ → ℂ) (s t : ℝ) (u v : ℂ) : Geodesic d₂ P s t u v ↔ Geodesic d₁ P s t u v := by
  unfold Geodesic
  simp only [isCurve_iff_of_dist_scale d₁ d₂ k hk0 hkt hd, len_eq_mul_of_dist_scale d₁ d₂ k hd, hd,
    ENNReal.mul_right_inj hk0 hkt, mul_lt_top_iff_of_ne hk0 hkt]

end Scaling

theorem ofReal_m_shift (ξ Q α r c t : ℝ) :
    ENNReal.ofReal ((1 - α)⁻¹ * (r ^ (ξ * Q) * Real.exp (ξ * (c + t)))) =
      ENNReal.ofReal (Real.exp (ξ * t)) * ENNReal.ofReal ((1 - α)⁻¹ * (r ^ (ξ * Q) * Real.exp (ξ * c))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_add, Real.exp_add]
  ring_nf

/-- regular pairs are homogeneous -/
theorem sourceRegularPair_scale_iff {d₁ d₂ : LSCMetric} {ξ : ℝ} (t : ℝ)
    (hd : ∀ x y, d₂ (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * d₁ (x, y))
    (Q : ℝ) (z u v : ℂ) (r α θ c : ℝ) :
    SupercriticalConformalCovariance.Regular.SourceRegularPair d₂ z u v r α θ (r ^ (ξ * Q) * Real.exp (ξ * (c + t))) ↔
      SupercriticalConformalCovariance.Regular.SourceRegularPair d₁ z u v r α θ (r ^ (ξ * Q) * Real.exp (ξ * c)) := by
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * t)) with hkdef
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold SupercriticalConformalCovariance.Regular.SourceRegularPair
  simp only [geodesic_scale_iff hk0 hkt hd, pointSphereDist_scale hk0 hkt hd,
    aroundRat_scale hk0 hkt hd, hd, ofReal_m_shift, ← hkdef, scale_le_scale_iff hk0 hkt,
    scale_le_iff hk0 hkt]

/-- **Homogeneity of the literal good event.** -/
theorem good_scale_iff {d₁ d₂ : LSCMetric} {e₁ e₂ : ℂ × ℂ → ℝ≥0∞} {ξ : ℝ} (t : ℝ)
    (hd : ∀ x y, d₂ (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * d₁ (x, y))
    (he : ∀ p, e₂ p = ENNReal.ofReal (Real.exp (ξ * t)) * e₁ p)
    (Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ)) (k c η : ℝ) :
    SupercriticalConformalCovariance.Improve.Good d₂ e₂ ξ Q z r q a K θ k (c + t) η ↔
      SupercriticalConformalCovariance.Improve.Good d₁ e₁ ξ Q z r q a K θ k c η := by
  set l : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * t)) with hldef
  have hl0 : l ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hlt : l ≠ ⊤ := ENNReal.ofReal_ne_top
  have harnd := aroundDist_eq_mul_of_dist_scale d₁ d₂ l hl0 hlt hd
  have hacr := acrossDist_eq_mul_of_dist_scale d₁ d₂ l hl0 hlt hd
  have hbar := barrier_scale hl0 hlt hd z r
  unfold SupercriticalConformalCovariance.Improve.Good SupercriticalConformalCovariance.GoodAnnulus.LiteralGood
  refine and_congr (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))) ?_
  · unfold SupercriticalConformalCovariance.GoodAnnulus.G1
    simp only [ibg_scale_iff hl0 hlt hd, harnd, hacr, scale_le_scale_iff hl0 hlt]
  · unfold SupercriticalConformalCovariance.GoodAnnulus.G2
    rw [harnd, hbar, ofReal_N_shift, mul_left_comm _ l, min_mul_mul_left]
    exact scale_le_iff hl0 hlt _ _
  · unfold SupercriticalConformalCovariance.GoodAnnulus.G3
    simp only [ibg_scale_iff hl0 hlt hd]
  · unfold SupercriticalConformalCovariance.GoodAnnulus.G4 E4Prop
    rw [harnd, hacr]
    exact scale_le_scale_iff hl0 hlt _ _ _
  · unfold SupercriticalConformalCovariance.Improve.G5
    refine forall₂_congr fun u v => ?_
    refine imp_congr (sourceRegularPair_scale_iff t hd Q z u v r a θ c) (imp_congr Iff.rfl ?_)
    rw [aroundRat_scale hl0 hlt hd, hbar, he, hd, mul_left_comm (ENNReal.ofReal k) l]
    exact imp_congr (scale_le_iff hl0 hlt _ _) (scale_le_scale_iff hl0 hlt _ _ _)

end SupercriticalConformalCovariance.BiLip.L51
