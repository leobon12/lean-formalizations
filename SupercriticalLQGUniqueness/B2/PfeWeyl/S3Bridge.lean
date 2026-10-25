import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Assembly
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.CouplingMeasurable
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem exists_canonical_heat_version (δ : Set.Ioi (0 : ℝ)) :
    ∃ V : DistC → C(ℂ, ℝ), Measurable V ∧
      ∀ᵐ g ∂normGFFLaw, ∀ z, V g z = heatMollify (δ : ℝ) g z := by
  obtain ⟨V, hVm, hV⟩ := PfeAxioms.exists_measurable_continuous_real_version normGFFLaw
    (fun g z => heatMollify (δ : ℝ) g z)
    (Measurable.of_eval fun z => LQGMetric.measurable_heatMollify_left (δ : ℝ) z)
    (LQGMetric.LFPP.ae_continuous_heatMollify_normGFFLaw δ.property.ne')
  refine ⟨V, hVm, ?_⟩
  filter_upwards [hV] with g hg z
  exact congrFun hg z

 
theorem measurable_rescaledLFPP_comp (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    {V : DistC → C(ℂ, ℝ)} (hVm : Measurable V) (p : ℂ × ℂ) :
    Measurable fun g => rescaledLFPP ξ a (V g) p := by
  have hX : ∀ z, Measurable fun g => V g z := fun z =>
    (continuous_eval_const z).measurable.comp hVm
  exact continuous_coe_ennreal_ereal.measurable.comp
    ((B2.LscTop.measurable_lfppDistance_comp hX ξ p).const_mul _)

 
theorem ae_eq_rescaledLFPP_of_joint_law (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    {V : DistC → C(ℂ, ℝ)} (hVm : Measurable V)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (hN : Ω' → DistC) (F : Ω' → ℂ × ℂ → EReal)
    (hFc : ∀ᵐ ω ∂P', Continuous (F ω))
    (hlaw : P'.map (fun ω => (hN ω, F ω)) =
      normGFFLaw.map (fun g => (g, rescaledLFPP ξ a (V g)))) :
    ∀ᵐ ω ∂P', F ω = rescaledLFPP ξ a (V (hN ω)) := by
  obtain ⟨hprob, hcan⟩ := PfeAxioms.normalized_canonical_model
  have hsrc : Measurable (fun g : DistC => (g, rescaledLFPP ξ a (V g))) :=
    measurable_id.prodMk (Measurable.of_eval fun p => measurable_rescaledLFPP_comp ξ a hVm p)
  have hmeas : AEMeasurable (fun ω => (hN ω, F ω)) P' :=
    PfeAxioms.aemeasurable_of_map_eq_nondirac normGFFLaw P' _ _ hsrc.aemeasurable
      (fun x => PfeAxioms.gff_joint_law_ne_dirac normGFFLaw id hcan.1
        (fun g => rescaledLFPP ξ a (V g))
        (Measurable.of_eval fun p => measurable_rescaledLFPP_comp ξ a hVm p).aemeasurable x)
      hlaw
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (ℂ × ℂ)
  let Γ : Set (DistC × (ℂ × ℂ → EReal)) :=
    ⋂ k : ℕ, {x | x.2 (d k) = rescaledLFPP ξ a (V x.1) (d k)}
  have hΓ : MeasurableSet Γ := MeasurableSet.iInter fun k =>
    measurableSet_eq_fun ((measurable_pi_apply (d k)).comp measurable_snd)
      ((measurable_rescaledLFPP_comp ξ a hVm (d k)).comp measurable_fst)
  have hsrcΓ : (normGFFLaw.map (fun g => (g, rescaledLFPP ξ a (V g)))) Γᶜ = 0 := by
    rw [Measure.map_apply hsrc hΓ.compl]
    have : (fun g : DistC => (g, rescaledLFPP ξ a (V g))) ⁻¹' Γᶜ = ∅ := by
      ext g
      simp [Γ]
    rw [this, measure_empty]
  have hΓae : ∀ᵐ ω ∂P', (hN ω, F ω) ∈ Γ := by
    rw [ae_iff]
    have h0 := hsrcΓ
    rw [← hlaw, Measure.map_apply_of_aemeasurable hmeas hΓ.compl] at h0
    exact h0
  filter_upwards [hΓae, hFc] with ω hω hc
  refine Continuous.ext_on hd hc (B2.LscTop.continuous_rescaledLFPP ξ a _) ?_
  rintro _ ⟨k, rfl⟩
  exact Set.mem_iInter.1 hω k

 
theorem hconv_of_identification (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (Φ : DistC → LSCMetric)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC) (F : ℕ → Ω' → ℂ × ℂ → EReal)
    (L : Ω' → LSCMetric)
    (hid : ∀ n, ∀ᵐ ω ∂P', F n ω = rescaledLFPP ξ (m (ε n)) (V (ε n) (hN n ω)))
    (hlim : ∀ᵐ ω ∂P', LSCTendsto (fun n => F n ω) (L ω).toLSCFun.1)
    (hII : ∀ᵐ ω ∂P', L ω = Φ (h' ω)) :
    ∀ᵐ ω ∂P', Tendsto (fun n =>
      normalizedLFPPMetric ξ (m (ε n)) (V (ε n) (hN n ω))) atTop (𝓝 (Φ (h' ω))) := by
  filter_upwards [ae_all_iff.2 hid, hlim, hII] with ω hid' hl hL
  rw [tendsto_normalizedLFPP_iff_lscTendsto, ← hL]
  have hfun : (fun n => rescaledLFPP ξ (m (ε n)) (V (ε n) (hN n ω))) = fun n => F n ω := by
    funext n
    exact (hid' n).symm
  rw [hfun]
  exact hl

 


theorem happrox_of_continuous_approx (Φ : DistC → LSCMetric)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (hN : ℕ → Ω' → DistC) (h' : Ω' → DistC)
    (hNconv : ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω)))
    (hlusin : ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧ Continuous Ψ ∧
      normGFFLaw {g | Φ g ≠ Ψ g} < κ) :
    ∀ κ : ℝ≥0∞, 0 < κ → ∃ Ψ : DistC → LSCMetric, Measurable Ψ ∧
      normGFFLaw {g | Φ g ≠ Ψ g} < κ ∧
      ∀ᵐ ω ∂P', Tendsto (fun n => Ψ (hN n ω)) atTop (𝓝 (Ψ (h' ω))) := by
  intro κ hκ
  obtain ⟨Ψ, hΨm, hΨc, hΨ⟩ := hlusin κ hκ
  refine ⟨Ψ, hΨm, hΨ, ?_⟩
  filter_upwards [hNconv] with ω hω
  exact (hΨc.tendsto _).comp hω

end SupercriticalLQGUniqueness.B2.PfeWeyl
