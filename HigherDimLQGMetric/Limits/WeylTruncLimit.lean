import HigherDimLQGMetric.Limits.TruncApprox
import HigherDimLQGMetric.Trunc.LFPP

/-! Truncated-kernel part of corrected [1] Lemma 3.6. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6c_lemma36_trunc {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hL2c : L2c_trunc)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P)
    (hlim : ∀ᵐ ω ∂P, (Dh ω).IsLength ∧ IsProperFn (Dh ω).1 ∧
      ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn (fun n => ⇑(lfppSeq κ ξ εs (h ω) n))
          ⇑(Dh ω).1 atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) :
    ∀ᵐ ω ∂P,
      ∀ (fn : ℕ → C(Rd d, ℝ)) (f : C(Rd d, ℝ)) (M : ℝ),
        (∀ n z, |fn n z| ≤ M) →
        (∀ R : ℝ, 0 < R →
          TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop (closedBall 0 R)) →
        ∀ R : ℝ, 0 < R →
          TendstoUniformlyOn
            (fun n (p : Rd d × Rd d) =>
              (aEps κ ξ (εs n))⁻¹ *
                fieldLfpp ξ (truncMollify κ (εs n)
                  (addFun (h ω) (fn n))) p)
            (fun p => (weylScale ξ f (Dh ω) p.1 p.2).toReal)
            atTop (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (convMollify κ (εs n) (h ω)) :=
    ae_all_iff.mpr fun n => l10a_ae_continuous_convMollify hd κ hκ P h hh (hεs n)
  have hfield := hL2c d hd κ hκ P h hh
  filter_upwards [hlim, hc, hfield] with ω hω hcω htruncω
  intro fn f M hfnM hconv R hR
  have ha (n : ℕ) : 0 < aEps κ ξ (εs n) :=
    l6a_aEps_pos hd κ hκ ξ (hεs n)
  have hfM : ∀ z, |f z| ≤ M := by
    intro z
    have hz : z ∈ closedBall (0 : Rd d) (‖z‖ + 1) := by
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have ht := ((hconv (‖z‖ + 1) (by positivity)).tendsto_at hz).abs
    exact le_of_tendsto ht (Filter.Eventually.of_forall fun n => hfnM n z)
  let φ : ℕ → C(Rd d, ℝ) := fun n => ⟨convMollify κ (εs n) (h ω), hcω n⟩
  let G : ℕ → C(Rd d, ℝ) := fun n =>
    ⟨fun z => truncMollify κ (εs n) (addFun (h ω) (fn n)) z -
      convMollify κ (εs n) (h ω) z,
      (l2c_continuous_truncMollify hd hκ (hεs n) (addFun (h ω) (fn n))).sub
        (hcω n)⟩
  let Dn : ℕ → ContMetric d := fun n =>
    (fieldLfppMetric ξ (φ n)).smul (aEps κ ξ (εs n))⁻¹ (inv_pos.mpr (ha n))
  have hDn (n : ℕ) : (Dn n).IsLength :=
    ContMetric.isLength_smul (inv_pos.mpr (ha n))
      (fieldLfppMetric_isLength ξ (φ n))
  have hEq (n : ℕ) : (Dn n).1 = lfppSeq κ ξ εs (h ω) n := by
    ext p
    have hf : lfppDist κ ξ (εs n) (h ω) = fieldLfpp ξ (convMollify κ (εs n) (h ω)) := by
      funext q
      exact (fieldLfpp_eq_lfppDistOn (hcω n) q).symm
    have hscaled : Continuous
        ((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (h ω)) := by
      rw [hf]
      exact (continuous_fieldLfpp (hcω n)).const_smul _
    rw [ContMetric.smul_apply]
    change _ = (toCMapRd ((aEps κ ξ (εs n))⁻¹ •
      lfppDist κ ξ (εs n) (h ω))) p
    rw [toCMapRd_apply_of_continuous hscaled]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact congrArg ((aEps κ ξ (εs n))⁻¹ * ·) (by
      change fieldLfpp ξ (convMollify κ (εs n) (h ω)) p = _
      exact (hf ▸ rfl))
  have hDconv : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑(Dh ω).1 atTop
        (closedBall (0 : Rd d) T ×ˢ closedBall (0 : Rd d) T) := by
    intro T hT
    simpa only [hEq] using hω.2.2 T hT
  have hεWithin : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεt, Filter.Eventually.of_forall hεs⟩
  have hGconv : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(G n)) ⇑f atTop (closedBall (0 : Rd d) T) := by
    intro T hT
    have hH : TendstoUniformlyOn
        (fun n z => truncMollify κ (εs n) (h ω) z -
          convMollify κ (εs n) (h ω) z) 0 atTop
        (closedBall (0 : Rd d) T) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro η hη
      have ht := Metric.tendstoUniformlyOn_iff.mp (htruncω T hT) η hη
      filter_upwards [hεWithin.eventually ht] with n hn z hz
      have hnz := hn z hz
      rw [Real.dist_eq] at hnz ⊢
      have heq : 0 - (truncMollify κ (εs n) (h ω) z -
          convMollify κ (εs n) (h ω) z) =
          -(0 - (convMollify κ (εs n) (h ω) z -
            truncMollify κ (εs n) (h ω) z)) := by ring
      simp only [Pi.zero_apply] at hnz ⊢
      rw [heq, abs_neg]
      exact hnz
    have hF := l6c_tendstoUniformlyOn_truncMollify_seq hd κ hκ
      hεs hεt hfnM hfM hconv hT
    have hsum := hH.add hF
    convert hsum using 1
    · funext n z
      change truncMollify κ (εs n) (addFun (h ω) (fn n)) z -
        convMollify κ (εs n) (h ω) z =
        (truncMollify κ (εs n) (h ω) z -
          convMollify κ (εs n) (h ω) z) +
          truncMollify κ (εs n) (ofCont (fn n)) z
      rw [l6c_truncMollify_addFun]
      ring
    · simp
  have hW := l6d_weylCont d ξ Dn (Dh ω) G f hDn hω.1 hω.2.1
    hDconv hGconv ⟨M, hfM⟩ R hR
  refine hW.congr ?_
  filter_upwards with n
  intro p hp
  have heq := l6c_scaledLfpp_weyl_field ξ (aEps κ ξ (εs n)) (ha n)
    (φ n) (G n) p.1 p.2
  have hfieldEq : ((⇑(φ n) : Rd d → ℝ) + ⇑(G n)) =
      truncMollify κ (εs n) (addFun (h ω) (fn n)) := by
    funext z
    dsimp [φ, G]
    ring
  rw [hfieldEq] at heq
  exact heq

end HigherDimLQGMetric
