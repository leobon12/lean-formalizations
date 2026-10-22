import HigherDimLQGMetric.Limits.WeylLFPP
import HigherDimLQGMetric.Limits.LengthLFPP
import HigherDimLQGMetric.Weak.DetWeylCont

/-! Almost sure Weyl convergence along a locally uniformly convergent LFPP sequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The full-kernel part of corrected [1] Lemma 3.6.  The event is independent
of the bounded sequence of continuous perturbations. -/
theorem l6c_lemma36_full {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
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
                lfppDist κ ξ (εs n) (addFun (h ω) (fn n)) p)
            (fun p => (weylScale ξ f (Dh ω) p.1 p.2).toReal)
            atTop (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (convMollify κ (εs n) (h ω)) :=
    ae_all_iff.mpr fun n => l10a_ae_continuous_convMollify hd κ hκ P h hh (hεs n)
  have hadd := l2b_ae_convMollify_addFun d hd κ hκ P h hh
  filter_upwards [hlim, hc, hadd] with ω hω hcω haω
  intro fn f M hfnM hconv R hR
  have ha (n : ℕ) : 0 < aEps κ ξ (εs n) :=
    l6a_aEps_pos hd κ hκ ξ (hεs n)
  let φ : ℕ → C(Rd d, ℝ) := fun n => ⟨convMollify κ (εs n) (h ω), hcω n⟩
  let G : ℕ → C(Rd d, ℝ) := fun n =>
    ⟨convMollify κ (εs n) (ofCont (fn n)),
      l6c_continuous_convMollify_ofCont hd κ hκ (hεs n) (fn n) (hfnM n)⟩
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
  have hDconv : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑(Dh ω).1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    intro T hT
    simpa only [hEq] using hω.2.2 T hT
  have hGconv : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n => ⇑(G n)) ⇑f atTop (closedBall (0 : Rd d) T) := by
    intro T hT
    exact l6c_tendstoUniformlyOn_convMollify_seq hd κ hκ hεs hεt hfnM
      (fun z => by
        have hpoint : Tendsto (fun n => fn n z) atTop (𝓝 (f z)) := by
          have hz : z ∈ closedBall (0 : Rd d) (‖z‖ + 1) := by
            simp only [mem_closedBall, dist_zero_right]
            linarith
          exact (hconv (‖z‖ + 1) (by positivity)).tendsto_at hz
        have := hpoint.abs
        exact le_of_tendsto this (Filter.Eventually.of_forall fun n => hfnM n z))
      hconv hT
  have hfM : ∀ z, |f z| ≤ M := by
    intro z
    have hz : z ∈ closedBall (0 : Rd d) (‖z‖ + 1) := by
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have ht := ((hconv (‖z‖ + 1) (by positivity)).tendsto_at hz).abs
    exact le_of_tendsto ht (Filter.Eventually.of_forall fun n => hfnM n z)
  have hW := l6d_weylCont d ξ Dn (Dh ω) G f hDn hω.1 hω.2.1
    hDconv hGconv ⟨M, hfM⟩ R hR
  refine hW.congr ?_
  filter_upwards with n
  intro p hp
  have hsum (z : Rd d) : convMollify κ (εs n) (addFun (h ω) (fn n)) z =
      convMollify κ (εs n) (h ω) z + convMollify κ (εs n) (ofCont (fn n)) z := by
    rw [haω (εs n) (hεs n) z (fn n) M (hfnM n)]
    rw [l2b_convMollify_ofCont hd hκ (hεs n) (fn n) M (hfnM n) z]
  exact (l6c_scaledLfpp_addFun_weyl κ ξ (εs n) (aEps κ ξ (εs n)) (ha n)
    (h ω) (fn n) (hcω n)
    (l6c_continuous_convMollify_ofCont hd κ hκ (hεs n) (fn n) (hfnM n))
    hsum p.1 p.2)

end HigherDimLQGMetric
