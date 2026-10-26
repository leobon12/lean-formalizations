import SupercriticalConformalCovariance.Tangent.TangentLimit

/-!
# Lemma 3.3, display (5): joint convergence in law

`tangent_limit_law`: `(h, d_n, e_n) ⇒ (h, D_h, D_h)` jointly in law, the field read through its
Polish coordinates `pairJ ⊤ h` (LQGMetric) and the metrics in the compact Polish space `LSCFun`, for
any measurable `LSCFun`-valued versions `G n`, `E n` of `d_n`, `e_n`. It follows from the strong form
`tangent_limit` by the subsequence criterion and dominated convergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric Function
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open LQGMetric (DistC IsWholePlaneGFF restrictTo CoordJ pairJ)
open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric LSCTendsto IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open SupercriticalConformalCovariance.GM24 (isConformalBijection_invFunOn)

/-- **Lemma 3.3, (5)**: joint convergence in law of `(h, d_n, e_n)` to `(h, D_h, D_h)`. -/
theorem tangent_limit_law {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q) (hQpos : 0 < Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n))
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (G E : ℕ → Ω → LSCFun) (hGm : ∀ n, Measurable (G n)) (hEm : ∀ n, Measurable (E n))
    (hG : ∀ n, ∀ᵐ ω ∂P, (G n ω).1 = fun q => (extInternal (D (h ω)) (closedBall 0 (R n)) q : EReal))
    (hE : ∀ n, ∀ᵐ ω ∂P, (E n ω).1 = tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω)
    (F : BoundedContinuousFunction ((CoordJ → ℝ) × LSCFun × LSCFun) ℝ) :
    Tendsto (fun n => ∫ ω, F (pairJ ⊤ (h ω), G n ω, E n ω) ∂P) atTop
      (𝓝 (∫ ω, F (pairJ ⊤ (h ω), (D (h ω)).toLSCFun, (D (h ω)).toLSCFun) ∂P)) := by
  obtain ⟨hd, he⟩ := tangent_limit hQ hQpos hD hψ hexhaust hzero ha0 ha hR hRU P hh hbar fr hreal
  -- measurability of the integrands
  have hJ : Measurable fun ω => pairJ ⊤ (h ω) := (LQGMetric.measurable_pairJ ⊤).comp hh.measurable
  have hDm : Measurable fun ω => (D (h ω)).toLSCFun := by
    have := SupercriticalLQGUniqueness.B2.LscTop.borelSpace_LSCMetric
    exact (SupercriticalLQGUniqueness.B2.LscTop.measurable_toLSCFun).comp (hD.1.comp hh.measurable)
  haveI : SecondCountableTopology LSCFun := by
    letI := TopologicalSpace.metrizableSpaceMetric LSCFun
    infer_instance
  have hFm : Measurable fun x : (CoordJ → ℝ) × LSCFun × LSCFun => F x := F.continuous.measurable
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ms₁, hms₁, hae₁⟩ := hd (ns ∘ φ) hnsφ
  obtain ⟨ms₂, hms₂, hae₂⟩ := he (ns ∘ φ ∘ ms₁) (hnsφ.comp hms₁)
  refine ⟨φ ∘ ms₁ ∘ ms₂, ?_⟩
  have hGall : ∀ᵐ ω ∂P, ∀ n, (G n ω).1 =
      fun q => (extInternal (D (h ω)) (closedBall 0 (R n)) q : EReal) := ae_all_iff.2 hG
  have hEall : ∀ᵐ ω ∂P, ∀ n, (E n ω).1 =
      tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr n ω := ae_all_iff.2 hE
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
    (fun k => (hFm.comp (hJ.prodMk ((hGm _).prodMk (hEm _)))).aestronglyMeasurable)
    (integrable_const _) (fun k => Eventually.of_forall fun ω => F.norm_coe_le_norm _) ?_
  filter_upwards [hae₁, hae₂, hGall, hEall] with ω h1 h2 hGω hEω
  have h1' := h1.comp_strictMono hms₂
  have hGt : Tendsto (fun k => G (ns (φ (ms₁ (ms₂ k)))) ω) atTop (𝓝 (D (h ω)).toLSCFun) := by
    rw [SupercriticalLQGUniqueness.LSCFun.tendsto_iff_lscTendsto]
    simp only [hGω]
    exact h1'
  have hEt : Tendsto (fun k => E (ns (φ (ms₁ (ms₂ k)))) ω) atTop (𝓝 (D (h ω)).toLSCFun) := by
    rw [SupercriticalLQGUniqueness.LSCFun.tendsto_iff_lscTendsto]
    simp only [hEω]
    exact h2
  exact (F.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds (hGt.prodMk_nhds hEt))

end SupercriticalConformalCovariance.Tangent
