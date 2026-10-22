import HigherDimLQGMetric.Locality.MarkedPerturbBounds

/-! Common truncated LFPP convergence for a scalar normalization and a
compactly supported field mark. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_ae_marked_two_trunc_subseq {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hL2c : L2c_trunc) (εs : ℕ → ℝ)
    (hεs : ∀ n, 0 < εs n) (hεt : Tendsto εs atTop (𝓝 0))
    (μ : Measure (DistRd d)) [IsProbabilityMeasure μ]
    (hhμ : IsNormalizedLGF (id : DistRd d → DistRd d) μ)
    {E : Type*} [MeasurableSpace E] (Q : Measure E)
    (Xlim : E → DistRd d) (Xn : ℕ → E → DistRd d)
    (hXn : ∀ n, Measurable (Xn n))
    (hlaw : ∀ n, Q.map (Xn n) = μ) (hlimlaw : Q.map Xlim = μ)
    (D : E → ContMetric d)
    (hgood : ∀ᵐ e ∂Q, (D e).IsLength ∧ IsProperFn (D e).1)
    (hfull : ∀ᵐ e ∂Q, Tendsto
      (fun n => lfppSeq κ ξ εs (Xn n e) n) atTop (𝓝 (D e).1))
    (cn : ℕ → E → ℝ) (c : E → ℝ)
    (Fn : ℕ → E → C(Rd d, ℝ)) (F : E → C(Rd d, ℝ))
    (hcn : ∀ᵐ e ∂Q, Tendsto (fun n => cn n e) atTop (𝓝 (c e)))
    (hFn : ∀ᵐ e ∂Q, Tendsto (fun n => Fn n e) atTop (𝓝 (F e)))
    (K : Set (Rd d)) (hK : IsCompact K)
    (hsupp : ∀ᵐ e ∂Q, ∀ n z, z ∉ K → Fn n e z = 0) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns k))
                (addConst (Xn (ns k) e) (-cn (ns k) e))) p)
          (fun p => (weylScale ξ (ContinuousMap.const (Rd d) (-c e))
            (D e) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) ∧
      (∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns k))
                (addConst (Xn (ns k) e) (-cn (ns k) e) -
                  ofCont (Fn (ns k) e))) p)
          (fun p => (weylScale ξ
            (ContinuousMap.const (Rd d) (-c e) - F e)
            (D e) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) := by
  obtain ⟨hb₁, hb₂, hc₁, hc₂⟩ :=
    l7a_marked_perturb_bounds Q cn c Fn F hcn hFn K hK hsupp
  obtain ⟨ns, hns, h₁, h₂⟩ :=
    l7a_ae_two_moving_weyl_trunc_subseq hd κ hκ ξ hL2c εs hεs hεt
      μ hhμ Q Xlim Xn hXn hlaw hlimlaw D hgood hfull
      (fun e => ContinuousMap.const (Rd d) (-c e))
      (fun e => ContinuousMap.const (Rd d) (-c e) - F e)
      (fun n e => ContinuousMap.const (Rd d) (-cn n e))
      (fun n e => ContinuousMap.const (Rd d) (-cn n e) - Fn n e)
      hb₁ hb₂ hc₁ hc₂
  refine ⟨ns, hns, ?_, ?_⟩
  · simpa only [addConst] using h₁
  · filter_upwards [h₂] with e he R hR
    have hg (k : ℕ) :
        addFun (Xn (ns k) e)
          (ContinuousMap.const (Rd d) (-cn (ns k) e) - Fn (ns k) e) =
        addConst (Xn (ns k) e) (-cn (ns k) e) - ofCont (Fn (ns k) e) := by
      simp only [addFun, addConst, sub_eq_add_neg, ofCont_add, ofCont_neg]
      abel
    simpa only [hg] using he R hR

end HigherDimLQGMetric
