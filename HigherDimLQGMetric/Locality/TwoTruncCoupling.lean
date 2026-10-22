import HigherDimLQGMetric.Locality.MovingWeylBounded

/-! Two bounded perturbations of the same moving-field Skorokhod sequence
converge on a common deterministic subsequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_ae_two_moving_weyl_trunc_subseq {d : ℕ} (hd : 2 ≤ d)
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
    (f₁ f₂ : E → C(Rd d, ℝ))
    (fn₁ fn₂ : ℕ → E → C(Rd d, ℝ))
    (hbound₁ : ∀ᵐ e ∂Q, ∃ M : ℝ, ∀ n z, |fn₁ n e z| ≤ M)
    (hbound₂ : ∀ᵐ e ∂Q, ∃ M : ℝ, ∀ n z, |fn₂ n e z| ≤ M)
    (hconv₁ : ∀ᵐ e ∂Q, Tendsto (fun n => fn₁ n e) atTop (𝓝 (f₁ e)))
    (hconv₂ : ∀ᵐ e ∂Q, Tendsto (fun n => fn₂ n e) atTop (𝓝 (f₂ e))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns k))
                (addFun (Xn (ns k) e) (fn₁ (ns k) e))) p)
          (fun p => (weylScale ξ (f₁ e) (D e) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) ∧
      (∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns k))
                (addFun (Xn (ns k) e) (fn₂ (ns k) e))) p)
          (fun p => (weylScale ξ (f₂ e) (D e) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) := by
  obtain ⟨ns₁, hns₁, hlim₁⟩ :=
    l7a_ae_moving_weyl_bounded_trunc_subseq hd κ hκ ξ hL2c εs hεs hεt
      μ hhμ Q Xlim Xn hXn hlaw hlimlaw D hgood hfull
      fn₁ f₁ hbound₁ hconv₁
  let ε' : ℕ → ℝ := fun n => εs (ns₁ n)
  let X' : ℕ → E → DistRd d := fun n => Xn (ns₁ n)
  have hfull' : ∀ᵐ e ∂Q, Tendsto
      (fun n => lfppSeq κ ξ ε' (X' n e) n) atTop (𝓝 (D e).1) := by
    filter_upwards [hfull] with e he
    simpa only [Function.comp_def, ε', X', lfppSeq] using
      he.comp hns₁.tendsto_atTop
  have hbound₂' : ∀ᵐ e ∂Q, ∃ M : ℝ,
      ∀ n z, |fn₂ (ns₁ n) e z| ≤ M :=
    hbound₂.mono fun e ⟨M, hM⟩ => ⟨M, fun n z => hM (ns₁ n) z⟩
  have hconv₂' : ∀ᵐ e ∂Q,
      Tendsto (fun n => fn₂ (ns₁ n) e) atTop (𝓝 (f₂ e)) :=
    hconv₂.mono fun e he => he.comp hns₁.tendsto_atTop
  obtain ⟨ns₂, hns₂, hlim₂⟩ :=
    l7a_ae_moving_weyl_bounded_trunc_subseq hd κ hκ ξ hL2c ε'
      (fun n => hεs (ns₁ n)) (hεt.comp hns₁.tendsto_atTop)
      μ hhμ Q Xlim X' (fun n => hXn (ns₁ n))
      (fun n => hlaw (ns₁ n)) hlimlaw D hgood hfull'
      (fun n => fn₂ (ns₁ n)) f₂ hbound₂' hconv₂'
  refine ⟨(fun k => ns₁ (ns₂ k)), hns₁.comp hns₂, ?_, ?_⟩
  · filter_upwards [hlim₁] with e he R hR
    intro u hu
    exact hns₂.tendsto_atTop.eventually ((he R hR) u hu)
  · simpa only [ε', X'] using hlim₂

end HigherDimLQGMetric
