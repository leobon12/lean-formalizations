import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.DyadicEvent
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.DyadicTransfer




set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

open LQGMetric (DistC)

 


theorem dyadic_ratio_f0_of_good_sample
    {Ω : Type} (h : Ω → DistC) (ω : Ω) (D : DistC → LSCMetric)
    (M : ℝ) (hM : 1 ≤ M)
    {q R : ℝ} (hq : 0 < q) (hq8 : q ≤ 1 / 8) (hR : 0 < R)
    (z₀ : ℂ)
    (hgood : dyadicGoodSample h D ((3 : ℝ) / 4) M q R hq hR z₀ ω)
    (hcut : q ≤ scaleCutoff ((3 : ℝ) / 4)
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal)
    {δ : ℝ} (hδ : 0 < δ) (hδq : δ ≤ q)
    (x : ℂ) (hx : x ∈ Metric.ball z₀ (2 * R))
    (K : Set ℂ) (hK : IsCompact K)
    {Pth : ℝ → ℂ} {T s : ℝ}
    (hs0 : 0 < s) (hsT : s < T)
    (hP : (D (h ω)).IsCurve Pth 0 T) (hPK : MapsTo Pth (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist ((D (h ω)).pt '' K)
        ((D (h ω)).pt (Pth u)) ((D (h ω)).pt (Pth v)) =
          ENNReal.ofReal (v - u))
    (hhit : dist (Pth s) x ≤ δ * R)
    (hKnear : ∀ n : ℕ,
      (annulusAt x ((dyadicScale q n) * R)
        ((dyadicScale q n) ^ ((3 : ℝ) / 4) * R)
        (mul_pos (dyadicScale_pos hq n) hR)
        (mul_lt_mul_of_pos_right
          (Real.self_lt_rpow_of_lt_one (dyadicScale_pos hq n)
            (lt_of_le_of_lt (dyadicScale_le hq.le n) (by linarith : q < 1))
            (by norm_num)) hR)).toSet ⊆ K)
    (h0near : ∀ n : ℕ,
      (dyadicScale q n) ^ ((3 : ℝ) / 4) * R ≤ dist (Pth 0) x)
    (hTnear : ∀ n : ℕ,
      (dyadicScale q n) ^ ((3 : ℝ) / 4) * R ≤ dist (Pth T) x) :
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
  dsimp only
  obtain ⟨n, hδl, hl2δ, hl0, hlq⟩ := exists_dyadic_near hq hδ hδq
  let l := dyadicScale q n
  have hl : 0 < l := dyadicScale_pos hq n
  have hl1 : l < 1 := by linarith [dyadicScale_le hq.le n]
  have hlcut : l ≤ scaleCutoff ((3 : ℝ) / 4)
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal :=
    (dyadicScale_le hq.le n).trans hcut
  let small := annulusAt x (l * R) (l ^ ((3 : ℝ) / 4) * R)
    (mul_pos hl hR)
    (mul_lt_mul_of_pos_right
      (Real.self_lt_rpow_of_lt_one hl hl1 (by norm_num)) hR)
  have hA : small.toSet ⊆ K := hKnear n
  have hsmall : aroundDist (D (h ω)) small ≤
      ENNReal.ofReal (l ^
        (ratioExponent ((3 : ℝ) / 4)
          (ENNReal.ofReal M * ENNReal.ofReal M).toReal / 2)) *
          acrossDist (D (h ω)) small := by
    have hsample := hgood n
    rcases hsample with ⟨hB, hL, hfin, hcount⟩
    apply finite_scale_ratio_of_good_sample h ω D hl hl1 hR
      (by norm_num : (3 : ℝ) / 4 < 1) hM z₀ hB hL
      (by simpa only [l] using hfin)
      (by simpa only [l] using hcount) hlcut small hx rfl rfl K hK hA
      hs0 hsT hP hPK hgeo (h0near n) (hTnear n)
    exact (hhit.trans (mul_le_mul_of_nonneg_right hδl hR.le))
  have hcost0 : (ENNReal.ofReal M * ENNReal.ofReal M) ≠ 0 := by
    exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne'
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne').ne'
  have hcosttop : (ENNReal.ofReal M * ENNReal.ofReal M) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hβ : 0 < ratioExponent ((3 : ℝ) / 4)
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal / 2 :=
    div_pos (ratioExponent_pos (by norm_num)
      (ENNReal.toReal_pos hcost0 hcosttop)) (by norm_num)
  have hB := (hgood n).1
  have hL := (hgood n).2.1
  have htransfer := ratio_of_nearby_scale (D (h ω)) hB hL hδ
    (hδq.trans hq8) hδl hl2δ hR hβ x hsmall
  have hexp : ratioExponent ((3 : ℝ) / 4)
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal / 2 / 2 =
      ratioExponent ((3 : ℝ) / 4)
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal / 4 := by ring
  rw [hexp] at htransfer
  exact htransfer


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
