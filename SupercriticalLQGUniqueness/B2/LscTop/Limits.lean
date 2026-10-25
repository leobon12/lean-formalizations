import SupercriticalLQGUniqueness.B2.LscTop.Compact
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

 

















set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory

namespace SupercriticalLQGUniqueness.B2.LscTop

instance instNonemptyLSCFun : Nonempty LSCFun := ⟨⟨fun _ => ⊤, lowerSemicontinuous_const⟩⟩

 
def euclideanLSCMetric : LSCMetric :=
  ⟨fun p => edist p.1 p.2,
    ⟨fun x => edist_self x, fun _ _ h => edist_eq_zero.1 h, fun x y => edist_comm x y,
      fun x y z => edist_triangle x y z⟩,
    continuous_edist.lowerSemicontinuous⟩

instance instNonemptyLSCMetric : Nonempty LSCMetric := ⟨euclideanLSCMetric⟩

 
theorem borelSpace_LSCMetric : BorelSpace LSCMetric := ⟨rfl⟩

 

theorem lscTendsto_limUnder {F : ℕ → LSCFun}
    (h : ∃ f : LSCFun, LSCTendsto (fun n => (F n).1) f.1) :
    LSCTendsto (fun n => (F n).1) (limUnder atTop F).1 := by
  obtain ⟨f, hf⟩ := h
  exact LSCFun.lscTendsto_of_tendsto (tendsto_nhds_limUnder ⟨f, LSCFun.tendsto_of_lscTendsto hf⟩)

variable {Ω : Type*} [MeasurableSpace Ω]

 

section LSCFun

variable [MeasurableSpace LSCFun] [BorelSpace LSCFun]

 

theorem measurableSet_exists_tendsto {F : ℕ → Ω → LSCFun} (hF : ∀ n, Measurable (F n)) :
    MeasurableSet {ω | ∃ f : LSCFun, Tendsto (fun n => F n ω) atTop (𝓝 f)} :=
  MeasureTheory.measurableSet_exists_tendsto hF

 
theorem measurableSet_exists_lscTendsto {F : ℕ → Ω → LSCFun} (hF : ∀ n, Measurable (F n)) :
    MeasurableSet {ω | ∃ f : LSCFun, LSCTendsto (fun n => (F n ω).1) f.1} := by
  simpa only [LSCFun.tendsto_iff_lscTendsto] using measurableSet_exists_tendsto hF

 
theorem measurable_limUnder {F : ℕ → Ω → LSCFun} (hF : ∀ n, Measurable (F n)) :
    Measurable fun ω => limUnder atTop fun n => F n ω :=
  (StronglyMeasurable.limUnder fun n => (hF n).stronglyMeasurable).measurable

 

theorem measurableSet_lscTendsto {F : ℕ → Ω → LSCFun} (hF : ∀ n, Measurable (F n))
    {L : Ω → LSCFun} (hL : Measurable L) :
    MeasurableSet {ω | LSCTendsto (fun n => (F n ω).1) (L ω).1} := by
  simpa only [LSCFun.tendsto_iff_lscTendsto] using measurableSet_tendsto_fun (l := atTop) hF hL

 
theorem measurable_of_lscTendsto {F : ℕ → Ω → LSCFun} (hF : ∀ n, Measurable (F n))
    {L : Ω → LSCFun} (h : ∀ ω, LSCTendsto (fun n => (F n ω).1) (L ω).1) : Measurable L :=
  measurable_of_tendsto_metrizable hF
    (tendsto_pi_nhds.2 fun ω => LSCFun.tendsto_of_lscTendsto (h ω))

 

theorem aemeasurable_of_lscTendsto_ae {μ : Measure Ω} {F : ℕ → Ω → LSCFun}
    (hF : ∀ n, AEMeasurable (F n) μ) {L : Ω → LSCFun}
    (h : ∀ᵐ ω ∂μ, LSCTendsto (fun n => (F n ω).1) (L ω).1) : AEMeasurable L μ :=
  aemeasurable_of_tendsto_metrizable_ae atTop hF
    (h.mono fun _ hω => LSCFun.tendsto_of_lscTendsto hω)

end LSCFun

 

section LSCMetric

 
theorem measurable_toLSCFun [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    Measurable LSCMetric.toLSCFun := by
  have := borelSpace_LSCMetric
  exact LSCMetric.isInducing_toLSCFun.continuous.measurable

 

theorem measurable_iff_toLSCFun [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {L : Ω → LSCMetric} : Measurable L ↔ Measurable fun ω => (L ω).toLSCFun := by
  refine ⟨fun h => measurable_toLSCFun.comp h, fun h => ?_⟩
  have hb : LSCMetric.instMeasurableSpace =
      MeasurableSpace.comap LSCMetric.toLSCFun ‹MeasurableSpace LSCFun› := by
    rw [BorelSpace.measurable_eq (α := LSCFun)]
    exact borel_comap
  rw [measurable_iff_comap_le, hb, MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 h

 
theorem measurable_of_tendsto_lscMetric {G : ℕ → Ω → LSCMetric} (hG : ∀ n, Measurable (G n))
    {L : Ω → LSCMetric} (h : ∀ ω, Tendsto (fun n => G n ω) atTop (𝓝 (L ω))) : Measurable L := by
  have := borelSpace_LSCMetric
  exact measurable_of_tendsto_metrizable hG (tendsto_pi_nhds.2 h)

 
theorem aemeasurable_of_tendsto_lscMetric_ae {μ : Measure Ω} {G : ℕ → Ω → LSCMetric}
    (hG : ∀ n, AEMeasurable (G n) μ) {L : Ω → LSCMetric}
    (h : ∀ᵐ ω ∂μ, Tendsto (fun n => G n ω) atTop (𝓝 (L ω))) : AEMeasurable L μ := by
  have := borelSpace_LSCMetric
  exact aemeasurable_of_tendsto_metrizable_ae atTop hG h

 

theorem measurable_limUnder_lscMetric {G : ℕ → Ω → LSCMetric} (hG : ∀ n, Measurable (G n))
    (h : ∀ ω, ∃ D : LSCMetric, Tendsto (fun n => G n ω) atTop (𝓝 D)) :
    Measurable fun ω => limUnder atTop fun n => G n ω :=
  measurable_of_tendsto_lscMetric hG fun ω => tendsto_nhds_limUnder (h ω)

 

theorem aemeasurable_limUnder_lscMetric {μ : Measure Ω} {G : ℕ → Ω → LSCMetric}
    (hG : ∀ n, AEMeasurable (G n) μ)
    (h : ∀ᵐ ω ∂μ, ∃ D : LSCMetric, Tendsto (fun n => G n ω) atTop (𝓝 D)) :
    AEMeasurable (fun ω => limUnder atTop fun n => G n ω) μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => G n ω) atTop (𝓝 (limUnder atTop fun n => G n ω)) := by
  have h' : ∀ᵐ ω ∂μ, Tendsto (fun n => G n ω) atTop (𝓝 (limUnder atTop fun n => G n ω)) :=
    h.mono fun _ hω => tendsto_nhds_limUnder hω
  exact ⟨aemeasurable_of_tendsto_lscMetric_ae hG h', h'⟩

 

theorem measurableSet_tendsto_lscMetric {G : ℕ → Ω → LSCMetric} (hG : ∀ n, Measurable (G n))
    {L : Ω → LSCMetric} (hL : Measurable L) :
    MeasurableSet {ω | Tendsto (fun n => G n ω) atTop (𝓝 (L ω))} := by
  have := borelSpace_LSCMetric
  exact measurableSet_tendsto_fun hG hL

 

theorem measurableSet_exists_lscTendsto_lscMetric [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {G : ℕ → Ω → LSCMetric} (hG : ∀ n, Measurable (G n)) :
    MeasurableSet {ω | ∃ f : LSCFun, LSCTendsto (fun n => (G n ω).toLSCFun.1) f.1} :=
  measurableSet_exists_lscTendsto fun n => measurable_toLSCFun.comp (hG n)

end LSCMetric

end SupercriticalLQGUniqueness.B2.LscTop
