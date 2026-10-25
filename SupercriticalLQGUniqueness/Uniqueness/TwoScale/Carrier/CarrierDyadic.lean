import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.CarrierGeometry




set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

open LQGMetric (DistC)

 


theorem carrier_dyadic_ratio_f0
    {Ω : Type} (h : Ω → DistC) (ω : Ω) (D : DistC → LSCMetric)
    (M : ℝ) (hM : 1 ≤ M)
    {q R : ℝ} (hq : 0 < q) (hq8 : q ≤ 1 / 8)
    (hqrad : q ^ ((3 : ℝ) / 4) ≤ 1 / 8) (hR : 0 < R)
    (z₀ : ℂ)
    (hgood : dyadicGoodSample h D ((3 : ℝ) / 4) M q R hq hR z₀ ω)
    (hcut : q ≤ scaleCutoff ((3 : ℝ) / 4)
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal)
    {δ : ℝ} (hδ : 0 < δ) (hδq : δ ≤ q)
    (x : ℂ) (hxlo : 3 * R / 4 ≤ dist x z₀)
    (hxhi : dist x z₀ ≤ 3 * R / 2)
    {Pth : ℝ → ℂ} {T s : ℝ}
    (hs0 : 0 < s) (hsT : s < T)
    (hP : (D (h ω)).IsCurve Pth 0 T)
    (hPK : MapsTo Pth (Icc 0 T)
      (closedBall z₀ (2 * R) \ ball z₀ (R / 2)))
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist ((D (h ω)).pt ''
        (closedBall z₀ (2 * R) \ ball z₀ (R / 2)))
        ((D (h ω)).pt (Pth u)) ((D (h ω)).pt (Pth v)) =
          ENNReal.ofReal (v - u))
    (h0 : dist (Pth 0) z₀ = R / 2 ∨ dist (Pth 0) z₀ = 2 * R)
    (hT : dist (Pth T) z₀ = R / 2 ∨ dist (Pth T) z₀ = 2 * R)
    (hhit : dist (Pth s) x ≤ δ * R) :
    let A := annulusAt x (δ * R) (δ ^ ((1 : ℝ) / 2) * R)
      (mul_pos hδ hR)
      (mul_lt_mul_of_pos_right
        (Real.self_lt_rpow_of_lt_one hδ (lt_of_le_of_lt hδq
          (by linarith : q < 1)) (by norm_num)) hR)
    aroundDist (D (h ω)) A ≤
      ENNReal.ofReal (δ ^
        (ratioExponent ((3 : ℝ) / 4)
          (ENNReal.ofReal M * ENNReal.ofReal M).toReal / 4)) *
          acrossDist (D (h ω)) A := by
  have hK : IsCompact (closedBall z₀ (2 * R) \ ball z₀ (R / 2)) :=
    (isCompact_closedBall z₀ (2 * R)).diff isOpen_ball
  have hx : x ∈ Metric.ball z₀ (2 * R) := by
    rw [mem_ball]
    linarith
  have hKnear (n : ℕ) :
      (annulusAt x ((dyadicScale q n) * R)
        ((dyadicScale q n) ^ ((3 : ℝ) / 4) * R)
        (mul_pos (dyadicScale_pos hq n) hR)
        (mul_lt_mul_of_pos_right
          (Real.self_lt_rpow_of_lt_one (dyadicScale_pos hq n)
            (lt_of_le_of_lt (dyadicScale_le hq.le n) (by linarith : q < 1))
            (by norm_num)) hR)).toSet ⊆
        closedBall z₀ (2 * R) \ ball z₀ (R / 2) := by
    exact small_annulus_subset_carrier hR (dyadicScale_pos hq n)
      (lt_of_le_of_lt (dyadicScale_le hq.le n) (by linarith : q < 1))
      z₀ x hxlo hxhi (dyadic_outer_radius_le_eighth hq hR hqrad n)
  have h0near (n : ℕ) :
      (dyadicScale q n) ^ ((3 : ℝ) / 4) * R ≤ dist (Pth 0) x := by
    have hrad := dyadic_outer_radius_le_eighth hq hR hqrad n
    have hdist := carrier_boundary_far hR z₀ x (Pth 0) hxlo hxhi h0
    linarith
  have hTnear (n : ℕ) :
      (dyadicScale q n) ^ ((3 : ℝ) / 4) * R ≤ dist (Pth T) x := by
    have hrad := dyadic_outer_radius_le_eighth hq hR hqrad n
    have hdist := carrier_boundary_far hR z₀ x (Pth T) hxlo hxhi hT
    linarith
  exact dyadic_ratio_f0_of_good_sample h ω D M hM hq hq8 hR z₀
    hgood hcut hδ hδq x hx _ hK hs0 hsT hP hPK hgeo hhit
    hKnear h0near hTnear


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
