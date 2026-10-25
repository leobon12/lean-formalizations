import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces
import LQGMetric.Field.CameronMartin




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open LQGMetric (DistC TestC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces

 
def IsOpenAnnularTubeV2 (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (U : TopologicalSpace.Opens ℂ) : Prop :=
  (U : Set ℂ) ⊆ {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)} ∧
  LQGMetric.Disconnects (U : Set ℂ) (Metric.sphere z r)
    (Metric.sphere z (3 * (r : ℝ)))

 
def sampleEvent {Ω : Type} (h : Ω → DistC) (E : Set DistC) : Set Ω := h ⁻¹' E

 


structure ObjectAtV2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (par : Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1) (z : ℂ) (r : Set.Ioi (0 : ℝ)) where
  U : TopologicalSpace.Opens ℂ
  V : TopologicalSpace.Opens ℂ
  f : TestC
  E : Set DistC
  U_annular : IsOpenAnnularTubeV2 z r U
  V_annular : IsOpenAnnularTubeV2 z r V
  closure_U_V : closure (U : Set ℂ) ⊆ (V : Set ℂ)
  closure_V_annulus : closure (V : Set ℂ) ⊆
    {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)}
  f_nonneg : ∀ x : ℂ, 0 ≤ f x
  f_le : ∀ x : ℂ, f x ≤ par.Cmax
  f_on_U : ∀ x ∈ (U : Set ℂ), f x = par.Cmax
  f_off_V : ∀ x ∉ (V : Set ℂ), f x = 0
  E_measurable : MeasurableSet E
  E_constant : ∀ u : DistC, ∀ c : ℝ,
    u ∈ E ↔ LQGMetric.addConst u c ∈ E
  E_local : ∃ E₀ : Set DistC,
    @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0
      (id : DistC → DistC)
      {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}) E₀ ∧
    E =ᵐ[P.map h] E₀
  E_probability : ENNReal.ofReal (pbar : ℝ) ≤ P (sampleEvent h E)
  E_circle : ∀ u ∈ E, ∃ c : ℝ, IsCircleAverage u r z c
  E_bounds : ∀ u ∈ E, ∀ c : ℝ, IsCircleAverage u r z c →
    let N : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c))
    OptimalConstants.Ratios.setDist (D u) (V : Set ℂ)
      (Metric.sphere z r ∪ Metric.sphere z (3 * (r : ℝ))) ≥
        ENNReal.ofReal par.Cacross * N ∧
    (∃ A : EuclideanAnnulus,
      A.center = z ∧ A.innerRadius = 3 * (r : ℝ) ∧
      A.outerRadius = 4 * (r : ℝ) ∧
      aroundDist (D u) A ≤ ENNReal.ofReal par.Caround * N) ∧
    HasTubeSeparator (D u) z r U (ENNReal.ofReal par.Ctube * N)
  E_rn : ∀ u ∈ E,
    par.Crn⁻¹ ≤ LQGMetric.cmDensity f (LQGMetric.pair0 u) ∧
      LQGMetric.cmDensity f (LQGMetric.pair0 u) ≤ par.Crn
  E_shortcut : ∀ u ∈ E, ∀ c : ℝ, IsCircleAverage u r z c →
    let d := D (LQGMetric.addFun u (-(LQGMetric.testCont f)))
    let e := D' (LQGMetric.addFun u (-(LQGMetric.testCont f)))
    let W := Metric.ball z (4 * (r : ℝ))
    let N := ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c))
    ∀ (P' : ℝ → ℂ) (T τ' τ σ σ' : ℝ),
      BumpedGeodesic d P' T → P' 0 ∉ W → P' T ∉ W →
      Excursion P' T W V τ' τ σ σ' →
      ∃ (hτ : P' τ ∈ W) (hσ : P' σ ∈ W),
        ENNReal.ofReal par.Ctime * N ≤
          (D u).internal W (⟨P' τ, hτ⟩, ⟨P' σ, hσ⟩) →
        ∃ s t : ℝ, τ ≤ s ∧ s < t ∧ t ≤ σ ∧
          ENNReal.ofReal par.Cinc * N ≤ ENNReal.ofReal (t - s) ∧
          ∃ (hs : P' s ∈ W) (ht : P' t ∈ W),
            e.internal W (⟨P' s, hs⟩, ⟨P' t, ht⟩) ≤
              ENNReal.ofReal (cMid * (t - s))

 
theorem ObjectAtV2.sample_measurable {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : Parameters ξ}
    {pbar : Set.Ioo (0 : ℝ) 1} {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : ObjectAtV2 P h D D' ξ Q cMid par pbar z r)
    (hh : IsNormalizedWholePlaneGFF h P) :
    MeasurableSet (sampleEvent h obj.E) := by
  exact obj.E_measurable.preimage hh.1.measurable

 
private theorem fieldSigmaClosed0_preimage {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (K : Set ℂ) (E₀ : Set DistC)
    (hm : @MeasurableSet DistC
      (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) E₀) :
    @MeasurableSet Ω (LQGMetric.Blueprint.fieldSigmaClosed0 h K) (h ⁻¹' E₀) := by
  unfold LQGMetric.Blueprint.fieldSigmaClosed0 at hm ⊢
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro ε
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro hε
  have he := (MeasurableSpace.measurableSet_iInf.mp
    (MeasurableSpace.measurableSet_iInf.mp hm ε) hε)
  unfold LQGMetric.Blueprint.fieldSigma0On at he ⊢
  obtain ⟨s, hs, hEs⟩ := MeasurableSpace.measurableSet_comap.mp he
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨s, hs, ?_⟩
  simpa only [Set.preimage_preimage, Function.comp_def, id_eq] using congrArg (fun t : Set DistC => h ⁻¹' t) hEs

 
theorem ObjectAtV2.sample_local {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : Parameters ξ}
    {pbar : Set.Ioo (0 : ℝ) 1} {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : ObjectAtV2 P h D D' ξ Q cMid par pbar z r)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ E₀ : Set Ω,
      @MeasurableSet Ω (LQGMetric.Blueprint.fieldSigmaClosed0 h
        {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}) E₀ ∧
      sampleEvent h obj.E =ᵐ[P] E₀ := by
  obtain ⟨E₀, hmeas, hae⟩ := obj.E_local
  refine ⟨h ⁻¹' E₀, fieldSigmaClosed0_preimage h _ E₀ hmeas, ?_⟩
  exact ae_of_ae_map hh.1.measurable.aemeasurable hae

 
theorem ObjectAtV2.sample_circle {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : Parameters ξ}
    {pbar : Set.Ioo (0 : ℝ) 1} {z : ℂ} {r : Set.Ioi (0 : ℝ)}
    (obj : ObjectAtV2 P h D D' ξ Q cMid par pbar z r)
    {ω : Ω} (hω : ω ∈ sampleEvent h obj.E) :
    ∃ c : ℝ, IsCircleAverage (h ω) r z c := obj.E_circle (h ω) hω

 
structure ObjectsExistV2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cMinus cPlus : ℝ≥0∞) (pbar : Set.Ioo (0 : ℝ) 1) where
  cMid' : ℝ
  cMid'_lower : cMinus.toReal < cMid'
  cMid'_upper : cMid' < midpoint cMinus cPlus
  radii : AdmissibleRadii
  params : Parameters ξ
  family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ radii.radii →
    ObjectAtV2 P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r
  density : ∀ κ : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ j : ℕ,
      let b : Set.Ioi (0 : ℝ) := dyadicRadius j
      ENNReal.ofReal (κ : ℝ) ≤
        P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κ
          ⟨cMid', lt_of_le_of_lt ENNReal.toReal_nonneg cMid'_lower⟩) →
      ∃ F : Finset ℝ,
        (F : Set ℝ) = radii.radii ∩ Set.Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) ∧
        (5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8) ≤ F.card

 
def CountingBadEventV2 {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cPlus : ℝ≥0∞)
    (R : AdmissibleRadii)
    (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set DistC)
    (b ε : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) : Set Ω :=
  CountingBadEvent h D D' ξ Q cPlus R
    (fun z r hr => sampleEvent h (event z r hr)) b ε K₁ K₂

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
