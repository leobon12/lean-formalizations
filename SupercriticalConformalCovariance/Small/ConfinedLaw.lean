import SupercriticalConformalCovariance.Tangent.Final

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set TopologicalSpace

namespace SupercriticalConformalCovariance.Small
open LQGMetric (DistC CoordJ pairJ)
open SupercriticalLQGUniqueness (LSCMetric LSCFun LSCTendsto)
open SupercriticalConformalCovariance.Tangent (SubseqLSC)

/-- Two diagonal-corrected metric families converging in probability to the same
metric converge jointly in law with the fixed field coordinate. -/
theorem confined_joint_law_of_subseq
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : Measurable h)
    (D E : ℕ → Ω → LSCMetric) (d : Ω → LSCMetric)
    (hDm : ∀ n, Measurable (D n)) (hEm : ∀ n, Measurable (E n))
    (hdm : Measurable d)
    (hD : SubseqLSC P (fun n ω q => (D n ω q : EReal))
      (fun ω q => (d ω q : EReal)))
    (hE : SubseqLSC P (fun n ω q => (E n ω q : EReal))
      (fun ω q => (d ω q : EReal)))
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (F : BoundedContinuousFunction ((CoordJ → ℝ) × LSCFun × LSCFun) ℝ) :
    Tendsto (fun n => ∫ ω,
        F (pairJ ⊤ (h ω), (D n ω).toLSCFun, (E n ω).toLSCFun) ∂P) atTop
      (𝓝 (∫ ω, F (pairJ ⊤ (h ω), (d ω).toLSCFun, (d ω).toLSCFun) ∂P)) := by
  have hJ : Measurable fun ω => pairJ ⊤ (h ω) :=
    (LQGMetric.measurable_pairJ ⊤).comp hh
  have hto : Measurable (LSCMetric.toLSCFun) :=
    SupercriticalLQGUniqueness.B2.LscTop.measurable_toLSCFun
  haveI : SecondCountableTopology LSCFun := by
    letI := TopologicalSpace.metrizableSpaceMetric LSCFun
    infer_instance
  have hFm : Measurable fun x : (CoordJ → ℝ) × LSCFun × LSCFun => F x :=
    F.continuous.measurable
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, hφ, hnsφ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨ms₁, hms₁, hae₁⟩ := hD (ns ∘ φ) hnsφ
  obtain ⟨ms₂, hms₂, hae₂⟩ := hE (ns ∘ φ ∘ ms₁) (hnsφ.comp hms₁)
  refine ⟨φ ∘ ms₁ ∘ ms₂, ?_⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
    (fun k => (hFm.comp
      (hJ.prodMk (((hto.comp (hDm _)).prodMk (hto.comp (hEm _)))))).aestronglyMeasurable)
    (integrable_const _) (fun k => Eventually.of_forall fun ω => F.norm_coe_le_norm _) ?_
  filter_upwards [hae₁, hae₂] with ω h1 h2
  have h1' := h1.comp_strictMono hms₂
  have hDt : Tendsto (fun k => (D (ns (φ (ms₁ (ms₂ k)))) ω).toLSCFun)
      atTop (𝓝 (d ω).toLSCFun) := by
    rw [SupercriticalLQGUniqueness.LSCFun.tendsto_iff_lscTendsto]
    exact h1'
  have hEt : Tendsto (fun k => (E (ns (φ (ms₁ (ms₂ k)))) ω).toLSCFun)
      atTop (𝓝 (d ω).toLSCFun) := by
    rw [SupercriticalLQGUniqueness.LSCFun.tendsto_iff_lscTendsto]
    exact h2
  exact (F.continuous.tendsto _).comp
    (tendsto_const_nhds.prodMk_nhds (hDt.prodMk_nhds hEt))

end SupercriticalConformalCovariance.Small
