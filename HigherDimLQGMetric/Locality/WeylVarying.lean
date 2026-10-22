import HigherDimLQGMetric.Locality.MovingTrunc
import HigherDimLQGMetric.Limits.WeylTruncLimit

/-! Deterministic truncated Weyl convergence for fields that vary with scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The varying-field version of the truncated part of Lemma 3.6. -/
theorem l7a_weyl_trunc_varying {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (gn : ℕ → DistRd d)
    (hc : ∀ n, Continuous (convMollify κ (εs n) (gn n)))
    (D : ContMetric d) (hDlen : D.IsLength) (hDprop : IsProperFn D.1)
    (hDconv : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(lfppSeq κ ξ εs (gn n) n)) ⇑D.1 atTop
        (closedBall (0 : Rd d) T ×ˢ closedBall (0 : Rd d) T))
    (htrunc : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn
        (fun n z => truncMollify κ (εs n) (gn n) z -
          convMollify κ (εs n) (gn n) z) 0 atTop
        (closedBall (0 : Rd d) T))
    (fn : ℕ → C(Rd d, ℝ)) (f : C(Rd d, ℝ)) (M : ℝ)
    (hfnM : ∀ n z, |fn n z| ≤ M)
    (hconv : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop (closedBall 0 T))
    (R : ℝ) (hR : 0 < R) :
    TendstoUniformlyOn
      (fun n (p : Rd d × Rd d) =>
        (aEps κ ξ (εs n))⁻¹ *
          fieldLfpp ξ (truncMollify κ (εs n)
            (addFun (gn n) (fn n))) p)
      (fun p => (weylScale ξ f D p.1 p.2).toReal) atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
  have ha (n : ℕ) : 0 < aEps κ ξ (εs n) :=
    l6a_aEps_pos hd κ hκ ξ (hεs n)
  have hfM : ∀ z, |f z| ≤ M := by
    intro z
    have hz : z ∈ closedBall (0 : Rd d) (‖z‖ + 1) := by
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have ht := ((hconv (‖z‖ + 1) (by positivity)).tendsto_at hz).abs
    exact le_of_tendsto ht (Filter.Eventually.of_forall fun n => hfnM n z)
  let φ : ℕ → C(Rd d, ℝ) := fun n => ⟨convMollify κ (εs n) (gn n), hc n⟩
  let G : ℕ → C(Rd d, ℝ) := fun n =>
    ⟨fun z => truncMollify κ (εs n) (addFun (gn n) (fn n)) z -
      convMollify κ (εs n) (gn n) z,
      (l2c_continuous_truncMollify hd hκ (hεs n) (addFun (gn n) (fn n))).sub
        (hc n)⟩
  let Dn : ℕ → ContMetric d := fun n =>
    (fieldLfppMetric ξ (φ n)).smul (aEps κ ξ (εs n))⁻¹ (inv_pos.mpr (ha n))
  have hDn (n : ℕ) : (Dn n).IsLength :=
    ContMetric.isLength_smul (inv_pos.mpr (ha n))
      (fieldLfppMetric_isLength ξ (φ n))
  have hEq (n : ℕ) : (Dn n).1 = lfppSeq κ ξ εs (gn n) n := by
    ext p
    have hf : lfppDist κ ξ (εs n) (gn n) =
        fieldLfpp ξ (convMollify κ (εs n) (gn n)) := by
      funext q
      exact (fieldLfpp_eq_lfppDistOn (hc n) q).symm
    have hscaled : Continuous
        ((aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (gn n)) := by
      rw [hf]
      exact (continuous_fieldLfpp (hc n)).const_smul _
    rw [ContMetric.smul_apply]
    change _ = (toCMapRd ((aEps κ ξ (εs n))⁻¹ •
      lfppDist κ ξ (εs n) (gn n))) p
    rw [toCMapRd_apply_of_continuous hscaled]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact congrArg ((aEps κ ξ (εs n))⁻¹ * ·) (by
      change fieldLfpp ξ (convMollify κ (εs n) (gn n)) p = _
      exact (hf ▸ rfl))
  have hDconv' : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
        (closedBall (0 : Rd d) T ×ˢ closedBall (0 : Rd d) T) := by
    intro T hT
    simpa only [hEq] using hDconv T hT
  have hGconv : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(G n)) ⇑f atTop (closedBall (0 : Rd d) T) := by
    intro T hT
    have hF := l6c_tendstoUniformlyOn_truncMollify_seq hd κ hκ
      hεs hεt hfnM hfM hconv hT
    have hsum := (htrunc T hT).add hF
    convert hsum using 1
    · funext n z
      change truncMollify κ (εs n) (addFun (gn n) (fn n)) z -
        convMollify κ (εs n) (gn n) z =
        (truncMollify κ (εs n) (gn n) z -
          convMollify κ (εs n) (gn n) z) +
          truncMollify κ (εs n) (ofCont (fn n)) z
      rw [l6c_truncMollify_addFun]
      ring
    · simp
  have hW := l6d_weylCont d ξ Dn D G f hDn hDlen hDprop
    hDconv' hGconv ⟨M, hfM⟩ R hR
  refine hW.congr ?_
  filter_upwards with n
  intro p hp
  have heq := l6c_scaledLfpp_weyl_field ξ (aEps κ ξ (εs n)) (ha n)
    (φ n) (G n) p.1 p.2
  have hfieldEq : ((⇑(φ n) : Rd d → ℝ) + ⇑(G n)) =
      truncMollify κ (εs n) (addFun (gn n) (fn n)) := by
    funext z
    dsimp [φ, G]
    ring
  rw [hfieldEq] at heq
  exact heq

end HigherDimLQGMetric
