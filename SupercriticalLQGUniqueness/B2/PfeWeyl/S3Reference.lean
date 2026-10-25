import SupercriticalLQGUniqueness.B2.PfeWeyl.S3LemProb
import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Transfer
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedLaw
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableHeatVersion
import SupercriticalLQGUniqueness.B2.LscTop.Metrizable

 
















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem normalizedLscLimit_of_coupling
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (Φ : DistC → LSCMetric) (hΦ : Measurable Φ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (h'm : Measurable h') (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (h'law : P'.map h' = normGFFLaw)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (V (ε n) (hN n ω))) atTop (𝓝 (Φ (h' ω))))
    (happrox : ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
      normGFFLaw {g | Φ g ≠ Ψ g} < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN n ω)) atTop (𝓝 (Ψ (h' ω)))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ NormalizedLscLimit ξ m (ε ∘ ns) Φ := by
  let _ : MetricSpace LSCMetric := TopologicalSpace.metrizableSpaceMetric LSCMetric
  have : BorelSpace LSCMetric := ⟨rfl⟩
  set R : ℕ → DistC → LSCMetric := fun n g =>
    normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (V (ε n) g) with hRdef
  have hR : ∀ n, Measurable (R n) := fun n =>
    PfeAxioms.measurable_normalizedLFPPMetric_comp (ξ : ℝ) _
      (fun z => (continuous_eval_const z).measurable.comp (hVm (ε n)))
  have happrox' : ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
      (∫⁻ g, min (edist (Φ g) (Ψ g)) 1 ∂normGFFLaw) < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN n ω)) atTop (𝓝 (Ψ (h' ω))) := by
    intro κ hκ
    obtain ⟨Ψ, hΨ, hlt, hconvΨ⟩ := happrox κ hκ
    refine ⟨Ψ, hΨ, lt_of_le_of_lt ?_ hlt, hconvΨ⟩
    have hmeas : MeasurableSet {g | Φ g ≠ Ψ g} := (measurableSet_eq_fun hΦ hΨ).compl
    calc (∫⁻ g, min (edist (Φ g) (Ψ g)) 1 ∂normGFFLaw)
        ≤ ∫⁻ g, {g | Φ g ≠ Ψ g}.indicator 1 g ∂normGFFLaw := by
          refine lintegral_mono fun g => ?_
          by_cases hg : Φ g = Ψ g
          · simp [hg]
          · have hmem : g ∈ {g | Φ g ≠ Ψ g} := hg
            rw [Set.indicator_of_mem hmem]
            exact min_le_right _ _
      _ = normGFFLaw {g | Φ g ≠ Ψ g} := lintegral_indicator_one hmeas
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_of_coupling normGFFLaw R Φ hR hΦ P' hN h'
    hNm h'm hNlaw h'law (fun n ω => R n (hN n ω)) (fun n => (hR n).comp (hNm n))
    (fun n => EventuallyEq.rfl) hconv happrox'
  refine ⟨ns, hns, ?_⟩
  intro Ω _ P _ h hh X hX
  have hlaw : P.map h = normGFFLaw := (PfeAxioms.normGFFLaw_eq_of_normalized P h hh).symm
  have h1 := hae P h hh.1.measurable.aemeasurable hlaw
  have hXe := PfeAxioms.ae_heat_smoothing_sequence_eq P h hh (ε ∘ ns) X hX
  have hVe : ∀ᵐ ω ∂P, ∀ n z, V (ε (ns n)) (h ω) z = heatMollify (ε (ns n) : ℝ) (h ω) z := by
    rw [ae_all_iff]
    intro n
    have := hV (ε (ns n))
    rw [← hlaw] at this
    exact ae_of_ae_map hh.1.measurable.aemeasurable this
  filter_upwards [h1, hXe, hVe] with ω hω hXω hVω
  have heq : ∀ k, X (ε (ns k)) ω = V (ε (ns k)) (h ω) := fun k =>
    ContinuousMap.ext fun z => (hXω k z).trans (hVω k z).symm
  have hfun : (fun k => normalizedLFPPMetric (ξ : ℝ) (m (ε (ns k))) (X (ε (ns k)) ω)) =
      fun k => R (ns k) (h ω) := by
    funext k
    rw [heq k]
  have hT : Tendsto (fun k => normalizedLFPPMetric (ξ : ℝ) (m (ε (ns k))) (X (ε (ns k)) ω))
      atTop (𝓝 (Φ (h ω))) := by
    rw [hfun]
    exact hω
  exact (tendsto_normalizedLFPP_iff_lscTendsto (ξ : ℝ) (fun k => m (ε (ns k)))
    (fun k => X (ε (ns k)) ω) (Φ (h ω))).1 hT

end SupercriticalLQGUniqueness.B2.PfeWeyl
