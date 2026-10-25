import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XMeasurableVersion
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircLemProb
import SupercriticalLQGUniqueness.B2.Final.CouplingData

 













set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open LQGMetric (DistC normGFFLaw CoordJ pairJ pairJInv)

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem exists_subseq_ae_of_coupled_field_determined
    {T : Type} [TopologicalSpace T] [TopologicalSpace.MetrizableSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] [Nonempty T]
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {e : ℕ → Set.Ioi (0 : ℝ)} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hB : Final.DG20CouplingData ξ Q m e c V P' h' hN L)
    (R : ℕ → DistC → T) (hR : ∀ n, Measurable (R n))
    (F : DistC → T)
    (hCoupled : ∀ᵐ ω ∂P', Tendsto (fun n => R n (hN n ω)) atTop (𝓝 (F (h' ω)))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ᵐ ω ∂P, Tendsto (fun n => R (ψ n) (h ω)) atTop (𝓝 (F (h ω))) := by
  letI : IsProbabilityMeasure normGFFLaw := PfeAxioms.normalized_canonical_model.1
  letI : IsProbabilityMeasure (normGFFLaw.map (pairJ ⊤)) :=
    (Measure.isProbabilityMeasure_map_iff (LQGMetric.measurable_pairJ ⊤).aemeasurable).2
      inferInstance
  letI : MetricSpace T := TopologicalSpace.metrizableSpaceMetric T
  have hFm : AEMeasurable (fun ω => F (h' ω)) P' :=
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun n => ((hR n).comp (hB.field_measurable n)).aemeasurable) hCoupled
  have hh'law : P'.map h' = normGFFLaw :=
    (PfeAxioms.normGFFLaw_eq_of_normalized P' h' hB.limit_field).symm
  obtain ⟨F₀, hF₀, hF₀eq⟩ :=
    exists_measurable_version_of_field_determined P' normGFFLaw h'
      hB.limit_field.1.measurable hh'law F hFm
  have hFcoupled : ∀ᵐ ω ∂P', F (h' ω) = F₀ (h' ω) := by
    apply ae_of_ae_map (μ := P') (p := fun g : DistC => F g = F₀ g)
      hB.limit_field.1.measurable.aemeasurable
    rw [hh'law]
    exact hF₀eq
  let μ : Measure (CoordJ → ℝ) := normGFFLaw.map (pairJ ⊤)
  let R' : ℕ → (CoordJ → ℝ) → T := fun n a => R n (pairJInv ⊤ a)
  let F' : (CoordJ → ℝ) → T := fun a => F₀ (pairJInv ⊤ a)
  have hR' : ∀ n, Measurable (R' n) := fun n =>
    (hR n).comp (LQGMetric.measurable_pairJInv ⊤)
  have hF' : Measurable F' := hF₀.comp (LQGMetric.measurable_pairJInv ⊤)
  have hh'm : Measurable h' := hB.limit_field.1.measurable
  have hXlaw : ∀ n, P'.map (fun ω => pairJ ⊤ (hN n ω)) = μ := by
    intro n
    change P'.map (pairJ ⊤ ∘ hN n) = μ
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) (hB.field_measurable n),
      hB.field_law n]
  have hXllaw : P'.map (fun ω => pairJ ⊤ (h' ω)) = μ := by
    change P'.map (pairJ ⊤ ∘ h') = μ
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) hh'm, hh'law]
  have hXconv : ∀ᵐ ω ∂P', Tendsto (fun n => pairJ ⊤ (hN n ω)) atTop
      (𝓝 (pairJ ⊤ (h' ω))) :=
    hB.field_tendsto.mono fun _ hw =>
      (PfeAxioms.continuous_pairJ_top.tendsto _).comp hw
  have hYconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      R' n (pairJ ⊤ (hN n ω))) atTop (𝓝 (F' (pairJ ⊤ (h' ω)))) := by
    filter_upwards [hCoupled, hFcoupled] with ω hω hFω
    simpa only [R', F', LQGMetric.pairJInv_pairJ, ← hFω] using hω
  obtain ⟨ψ, hψ, hae⟩ := PfeAxioms.exists_subseq_ae_of_coords_gen μ R' F'
    hR' hF' P' (fun n ω => pairJ ⊤ (hN n ω)) (fun ω => pairJ ⊤ (h' ω))
    (fun n => (LQGMetric.measurable_pairJ ⊤).comp (hB.field_measurable n))
    ((LQGMetric.measurable_pairJ ⊤).comp hh'm)
    hXlaw hXllaw hXconv hYconv
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ P _ h hh
  have hlaw : P.map (fun ω => pairJ ⊤ (h ω)) = μ := by
    change P.map (pairJ ⊤ ∘ h) = μ
    rw [← Measure.map_map (LQGMetric.measurable_pairJ ⊤) hh.1.measurable,
      ← PfeAxioms.normGFFLaw_eq_of_normalized P h hh]
  have h1 := hae P (fun ω => pairJ ⊤ (h ω))
    ((LQGMetric.measurable_pairJ ⊤).comp hh.1.measurable).aemeasurable hlaw
  have hFfixed : ∀ᵐ ω ∂P, F (h ω) = F₀ (h ω) := by
    apply ae_of_ae_map (μ := P) (p := fun g : DistC => F g = F₀ g)
      hh.1.measurable.aemeasurable
    rw [← PfeAxioms.normGFFLaw_eq_of_normalized P h hh]
    exact hF₀eq
  filter_upwards [h1, hFfixed] with ω hω hFω
  simpa only [R', F', LQGMetric.pairJInv_pairJ, ← hFω] using hω

end SupercriticalLQGUniqueness.B2.PfeWeyl
