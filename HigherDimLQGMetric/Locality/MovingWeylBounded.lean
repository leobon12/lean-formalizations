import HigherDimLQGMetric.Locality.MovingWeyl

/-! Weyl convergence for moving fields with samplewise globally bounded
perturbation sequences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_ae_moving_weyl_bounded_trunc_subseq {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hL2c : L2c_trunc) (εs : ℕ → ℝ)
    (hεs : ∀ n, 0 < εs n) (hεt : Tendsto εs atTop (𝓝 0))
    (μ : Measure (DistRd d)) [IsProbabilityMeasure μ]
    (hhμ : IsNormalizedLGF (id : DistRd d → DistRd d) μ)
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (Xlim : Ω → DistRd d) (Xn : ℕ → Ω → DistRd d)
    (hXn : ∀ n, Measurable (Xn n))
    (hlaw : ∀ n, Q.map (Xn n) = μ) (hlimlaw : Q.map Xlim = μ)
    (D : Ω → ContMetric d)
    (hgood : ∀ᵐ ω ∂Q, (D ω).IsLength ∧ IsProperFn (D ω).1)
    (hfull : ∀ᵐ ω ∂Q, Tendsto
      (fun n => lfppSeq κ ξ εs (Xn n ω) n) atTop (𝓝 (D ω).1))
    (fn : ℕ → Ω → C(Rd d, ℝ)) (f : Ω → C(Rd d, ℝ))
    (hbound : ∀ᵐ ω ∂Q, ∃ M : ℝ, ∀ n z, |fn n ω z| ≤ M)
    (hfconv : ∀ᵐ ω ∂Q, Tendsto (fun n => fn n ω) atTop (𝓝 (f ω))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns k))
                (addFun (Xn (ns k) ω) (fn (ns k) ω))) p)
          (fun p => (weylScale ξ (f ω) (D ω) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
  obtain ⟨ns, hns, herr⟩ :=
    l7a_exists_moving_trunc_error_subseq hd κ hκ hL2c εs hεs hεt μ
      hhμ Q Xlim Xn hXn hlaw hlimlaw
  have hc (n : ℕ) : ∀ᵐ ω ∂Q,
      Continuous (convMollify κ (εs n) (Xn n ω)) := by
    have hμc : ∀ᵐ g ∂μ, Continuous (convMollify κ (εs n) g) :=
      l10a_ae_continuous_convMollify hd κ hκ μ id hhμ (hεs n)
    have hQμ : ∀ᵐ g ∂Q.map (Xn n),
        Continuous (convMollify κ (εs n) g) := by
      rw [hlaw n]
      exact hμc
    exact ae_of_ae_map (hXn n).aemeasurable hQμ
  have hcall : ∀ᵐ ω ∂Q, ∀ n,
      Continuous (convMollify κ (εs n) (Xn n ω)) :=
    ae_all_iff.mpr hc
  refine ⟨ns, hns, ?_⟩
  filter_upwards [herr, hgood, hfull, hfconv, hbound, hcall]
    with ω he hg hf hfc hbd hcont
  intro R hR
  let ε' : ℕ → ℝ := fun k => εs (ns k)
  let g' : ℕ → DistRd d := fun k => Xn (ns k) ω
  let f' : ℕ → C(Rd d, ℝ) := fun k => fn (ns k) ω
  have hε' : ∀ k, 0 < ε' k := fun k => hεs (ns k)
  have hε't : Tendsto ε' atTop (𝓝 0) := hεt.comp hns.tendsto_atTop
  have hc' : ∀ k, Continuous (convMollify κ (ε' k) (g' k)) :=
    fun k => hcont (ns k)
  have hfull' : Tendsto (fun k => lfppSeq κ ξ ε' (g' k) k)
      atTop (𝓝 (D ω).1) := by
    simpa only [Function.comp_def, ε', g', lfppSeq] using
      hf.comp hns.tendsto_atTop
  have hfullR : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun k => ⇑(lfppSeq κ ξ ε' (g' k) k))
        ⇑(D ω).1 atTop
        (closedBall (0 : Rd d) T ×ˢ closedBall (0 : Rd d) T) := by
    intro T _
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hfull')
      _ ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have he' : Tendsto (fun k => l7a_truncErrorC hd κ hκ (ε' k)
      (hε' k) (g' k)) atTop (𝓝 (0 : C(Rd d, ℝ))) := he
  have hneg : Continuous (fun v : C(Rd d, ℝ) => -v) := by fun_prop
  have htruncC : Tendsto
      (fun k => -l7a_truncErrorC hd κ hκ (ε' k) (hε' k) (g' k))
      atTop (𝓝 (0 : C(Rd d, ℝ))) := by
    simpa only [Function.comp_def, neg_zero] using (hneg.tendsto 0).comp he'
  have htrunc : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn
        (fun k z => truncMollify κ (ε' k) (g' k) z -
          convMollify κ (ε' k) (g' k) z) 0 atTop
        (closedBall (0 : Rd d) T) := by
    intro T _
    have ht := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
      htruncC) _ (isCompact_closedBall (0 : Rd d) T)
    convert ht using 1
    · funext k z
      rw [ContinuousMap.neg_apply,
        l7a_truncErrorC_eq_of_continuous hd κ hκ
          (ε' k) (hε' k) (g' k) (hc' k) z]
      ring
    · rfl
  have hfc' : Tendsto f' atTop (𝓝 (f ω)) := hfc.comp hns.tendsto_atTop
  have hfcR : ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun k => ⇑(f' k)) ⇑(f ω) atTop
        (closedBall (0 : Rd d) T) := by
    intro T _
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hfc')
      _ (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hbd
  exact l7a_weyl_trunc_varying hd κ hκ ξ ε' hε' hε't g' hc'
    (D ω) hg.1 hg.2 hfullR htrunc f' (f ω) M
    (fun k z => hM (ns k) z) hfcR R hR

end HigherDimLQGMetric
