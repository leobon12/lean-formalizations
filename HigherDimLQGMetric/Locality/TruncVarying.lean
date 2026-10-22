import HigherDimLQGMetric.Locality.WeylVarying

/-! Moving-field approximation of the truncated metric by full LFPP. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- On a Skorokhod sequence whose full metrics converge, a vanishing compact-open
truncation error gives the same limit for the truncated metrics. -/
theorem l7a_trunc_metric_varying {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (gn : ℕ → DistRd d)
    (hc : ∀ n, Continuous (convMollify κ (εs n) (gn n)))
    (D : ContMetric d) (hDlen : D.IsLength) (hDprop : IsProperFn D.1)
    (hDconv : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(lfppSeq κ ξ εs (gn n) n)) ⇑D.1 atTop
        (closedBall (0 : Rd d) T ×ˢ closedBall (0 : Rd d) T))
    (herr : Tendsto
      (fun n => l7a_truncErrorC hd κ hκ (εs n) (hεs n) (gn n))
      atTop (𝓝 (0 : C(Rd d, ℝ))))
    (R : ℝ) (hR : 0 < R) :
    TendstoUniformlyOn
      (fun n (p : Rd d × Rd d) =>
        (aEps κ ξ (εs n))⁻¹ *
          fieldLfpp ξ (truncMollify κ (εs n) (gn n)) p)
      ⇑D.1 atTop
      (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
  have ha (n : ℕ) : 0 < aEps κ ξ (εs n) :=
    l6a_aEps_pos hd κ hκ ξ (hεs n)
  let φ : ℕ → C(Rd d, ℝ) := fun n => ⟨convMollify κ (εs n) (gn n), hc n⟩
  let G : ℕ → C(Rd d, ℝ) := fun n =>
    -l7a_truncErrorC hd κ hκ (εs n) (hεs n) (gn n)
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
  have hG : Tendsto G atTop (𝓝 (0 : C(Rd d, ℝ))) := by
    have hneg : Continuous (fun f : C(Rd d, ℝ) => -f) := by fun_prop
    simpa only [G, Function.comp_def, neg_zero] using (hneg.tendsto 0).comp herr
  have hGconv : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(G n)) (0 : Rd d → ℝ) atTop
        (closedBall (0 : Rd d) T) := by
    intro T _
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hG)
      _ (isCompact_closedBall _ _)
  have hW := l6d_weylCont d ξ Dn D G 0 hDn hDlen hDprop
    hDconv' hGconv ⟨0, by simp⟩ R hR
  have htarget : (fun p : Rd d × Rd d =>
      (weylScale ξ (0 : C(Rd d, ℝ)) D p.1 p.2).toReal) = ⇑D.1 := by
    funext p
    rw [show (0 : C(Rd d, ℝ)) = ContinuousMap.const (Rd d) 0 from rfl,
      weylScale_const_of_isLength hDlen]
    simp only [mul_zero, Real.exp_zero, one_mul]
    exact ENNReal.toReal_ofReal (D.nonneg p.1 p.2)
  rw [← htarget]
  refine hW.congr ?_
  filter_upwards with n
  intro p hp
  have heq := l6c_scaledLfpp_weyl_field ξ (aEps κ ξ (εs n)) (ha n)
    (φ n) (G n) p.1 p.2
  have hfieldEq : ((⇑(φ n) : Rd d → ℝ) + ⇑(G n)) =
      truncMollify κ (εs n) (gn n) := by
    funext z
    dsimp [φ, G]
    rw [l7a_truncErrorC_eq_of_continuous hd κ hκ
      (εs n) (hεs n) (gn n) (hc n) z]
    ring
  rw [hfieldEq] at heq
  exact heq

end HigherDimLQGMetric
