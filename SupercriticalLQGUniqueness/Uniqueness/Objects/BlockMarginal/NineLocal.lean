import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.TranslateLocal




 
















set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC restrictTo addConst)

theorem aeEventIn_inter {μ : Measure DistC} {K : Set ℂ} {E₁ E₂ : Set DistC}
    (h₁ : AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) K) E₁)
    (h₂ : AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) K) E₂) :
    AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) K) (E₁ ∩ E₂) := by
  obtain ⟨F₁, hF₁, he₁⟩ := h₁
  obtain ⟨F₂, hF₂, he₂⟩ := h₂
  exact ⟨F₁ ∩ F₂, hF₁.inter hF₂, he₁.inter he₂⟩

theorem aeEventIn_sigma0_closed0 {μ : Measure DistC} {V K : Set ℂ} (hVK : V ⊆ K)
    {E : Set DistC} (h : AEEventIn μ (fieldSigma0On (id : DistC → DistC) V) E) :
    AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) K) E := by
  obtain ⟨F, hF, he⟩ := h
  exact ⟨F, fieldSigma0On_le_closed0 hVK _ hF, he⟩

 
theorem aeEventIn_bool {ι : Type} [Fintype ι] (μ : Measure DistC) (K : Set ℂ)
    (E : ι → Set DistC) (hE : ∀ i, AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) K) (E i))
    (p : (ι → Prop) → Prop) :
    AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) K) {g | p (fun i => g ∈ E i)} := by
  choose F hFm hEF using hE
  refine ⟨{g | p (fun i => g ∈ F i)}, ?_, ?_⟩
  · have hΦ : @Measurable DistC (ι → Prop) (fieldSigmaClosed0 (id : DistC → DistC) K) _
        (fun g : DistC => fun i => g ∈ F i) := by
      refine @measurable_pi_iff DistC ι (fun _ => Prop)
        (fieldSigmaClosed0 (id : DistC → DistC) K) _ _ |>.2 fun i => ?_
      exact (@measurableSet_setOfPred DistC (fieldSigmaClosed0 (id : DistC → DistC) K)
        (fun g => g ∈ F i)).1 (hFm i)
    exact hΦ ((Set.toFinite {q : ι → Prop | p q}).measurableSet)
  · have hall : ∀ᵐ g ∂μ, ∀ i, (g ∈ E i) = (g ∈ F i) := ae_all_iff.2 fun i => hEF i
    filter_upwards [hall] with g hg
    rw [show (fun i => g ∈ E i) = (fun i => g ∈ F i) from funext hg]

theorem shiftSet_ball (z : ℂ) (R : ℝ) : shiftSet (ball (0 : ℂ) R) z = ball z R := by
  ext x
  simp only [shiftSet, mem_ofPred_eq, mem_ball, dist_eq_norm, sub_zero]

theorem shiftSet_bigAnn (C : Objects.CorrectedEvent.Constants) (z : ℂ) :
    shiftSet (bigAnn C) z = {x : ℂ | C.r ≤ dist x z ∧ dist x z ≤ 4 * C.r} := by
  ext x
  simp only [shiftSet, bigAnn, Objects.CorrectedEvent.cann, mem_ofPred_eq, dist_eq_norm, sub_zero]

 
theorem aeEventIn_S4 (μ : Measure DistC)
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ) (D D' : DistC → LSCMetric)
    (R : ℝ) (hR : ∀ k : Fin T.K, ball (Objects.CorrectedEvent.site T k) R ⊆ bigAnn C)
    (hBlock : AEEventIn μ (fieldSigma0On (id : DistC → DistC) (ball (0 : ℂ) R))
      {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g}) :
    AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) (bigAnn C))
      {g | Objects.CorrectedEvent.S4 C T (fun z => Objects.Excursions.blockEvent C T Ksh Cmid0 D D' z g)} := by
  have hsite : ∀ k : Fin T.K, AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) (bigAnn C))
      {g | Objects.Excursions.blockEvent C T Ksh Cmid0 D D' (Objects.CorrectedEvent.site T k) g} := by
    intro k
    have h1 := aeEventIn_normTranslate_sigma0 μ hμ (Objects.CorrectedEvent.site T k) (ball (0 : ℂ) R) hBlock
    rw [shiftSet_ball] at h1
    exact aeEventIn_sigma0_closed0 (hR k) h1
  exact aeEventIn_bool μ (bigAnn C) (fun k : Fin T.K => {g | Objects.Excursions.blockEvent C T Ksh Cmid0 D D' (Objects.CorrectedEvent.site T k) g})
    hsite (fun q => ∀ θ0 θ1 : ℝ, 0 ≤ θ1 - θ0 → θ1 - θ0 ≤ 2 * Real.pi →
      C.A_sp * C.r / 2 ≤ 2 * C.r * (θ1 - θ0) →
      ∃ k : Fin T.K, Objects.CorrectedEvent.onArc C.r θ0 θ1 (Objects.CorrectedEvent.site T k) ∧ q k)

 
theorem aeEventIn_correctedEvent (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (C : Objects.CorrectedEvent.Constants) (hCξ : C.ξ = ξ) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (Ksh : ℕ) (Cmid0 : ℝ)
    (R : ℝ) (hR : ∀ k : Fin T.K, ball (Objects.CorrectedEvent.site T k) R ⊆ bigAnn C)
    (hBlock : AEEventIn μ (fieldSigma0On (id : DistC → DistC) (ball (0 : ℂ) R))
      {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g})
    (hnar : C.A_nar < 1 / 6) (hρ : 0 < T.netRadius)
    (hS7 : ∀ x ∈ T.netSites, closedBall x (2 * T.netRadius) ⊆ bigAnn C)
    (hS8 : ∀ k : Fin T.K, ∀ l : Objects.CorrectedEvent.Cell, ∀ j ∈ Finset.Icc 1 (Objects.CorrectedEvent.supK C),
      closedBall (Objects.CorrectedEvent.cellCenter (Objects.CorrectedEvent.innerCenter T k) T.blockRadius l)
          (3 * Objects.CorrectedEvent.supRadius C j) ⊆ bigAnn C ∧
        closedBall (Objects.CorrectedEvent.cellCenter (Objects.CorrectedEvent.outerCenter T k) T.blockRadius l)
          (3 * Objects.CorrectedEvent.supRadius C j) ⊆ bigAnn C)
    (hS9 : tsupport (T.bump : ℂ → ℝ) ⊆ bigAnn C) :
    AEEventIn μ (fieldSigmaClosed0 (id : DistC → DistC) (bigAnn C))
      {g | Objects.CorrectedEvent.correctedEvent C T hData (Objects.Excursions.blockEvent C T Ksh Cmid0 D D') D D' g} := by
  have heq : {g | Objects.CorrectedEvent.correctedEvent C T hData (Objects.Excursions.blockEvent C T Ksh Cmid0 D D') D D' g} =
      {g | Objects.CorrectedEvent.S1 C (D g) g} ∩ ({g | Objects.CorrectedEvent.S2 C (D g) g} ∩ ({g | Objects.CorrectedEvent.S3 C (D g)} ∩
        ({g | Objects.CorrectedEvent.S4 C T (fun z => Objects.Excursions.blockEvent C T Ksh Cmid0 D D' z g)} ∩
          ({g | Objects.CorrectedEvent.S5 C (D g)} ∩ ({g | Objects.CorrectedEvent.S6 C (D g) g} ∩ ({g | Objects.CorrectedEvent.S7 C T (D g) g} ∩
            ({g | Objects.CorrectedEvent.S8 C T (D g)} ∩ {g | Objects.CorrectedEvent.S9 C T g}))))))) := by
    ext g
    simp only [Objects.CorrectedEvent.correctedEvent, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [heq]
  exact aeEventIn_inter (aeEventIn_S1 μ hμ ξ Q D hD C hCξ)
    (aeEventIn_inter (aeEventIn_S2 μ hμ ξ Q D hD C hCξ)
      (aeEventIn_inter (aeEventIn_S3 μ hμ ξ Q D hD C)
        (aeEventIn_inter (aeEventIn_S4 μ hμ C T Ksh Cmid0 D D' R hR hBlock)
          (aeEventIn_inter (aeEventIn_S5 μ hμ ξ Q D hD C hnar)
            (aeEventIn_inter (aeEventIn_S6 μ hμ ξ Q D hD C hCξ)
              (aeEventIn_inter (aeEventIn_S7 μ hμ ξ Q D hD C hCξ T hρ hS7)
                (aeEventIn_inter (aeEventIn_S8 μ hμ ξ Q D hD C T hS8)
                  (aeEventIn_S9 μ hμ ξ Q D hD C T hS9))))))))

 

theorem measure_preserving_normTranslate (μ : Measure DistC)
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ) (z : ℂ) :
    MeasurePreserving (Objects.Producer.normTranslate z) μ μ := by
  have hmap : μ.map (Objects.Producer.normTranslate z) = μ := by
    have := Objects.CentreEvent.map_normTranslate_fieldLaw_eq hμ z
    simpa only [Measure.map_id] using this
  exact MeasurePreserving.mk (Objects.BlockCoding.measurable_normTranslate z) hmap

 
theorem translate_representative (μ : Measure DistC)
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ) (C : Objects.CorrectedEvent.Constants)
    (L₀ Target : Set DistC)
    (hL₀ : MeasurableSet[fieldSigmaClosed0 (id : DistC → DistC) (bigAnn C)] L₀)
    (hnull : μ (L₀ \ Target) = 0) (z : ℂ) :
    MeasurableSet[fieldSigmaClosed0 (id : DistC → DistC)
        {x : ℂ | C.r ≤ dist x z ∧ dist x z ≤ 4 * C.r}] (Objects.Producer.normTranslate z ⁻¹' L₀) ∧
      μ (Objects.Producer.normTranslate z ⁻¹' L₀ \ Objects.Producer.centreTarget Target z) = 0 ∧
      μ (Objects.Producer.normTranslate z ⁻¹' L₀) = μ L₀ := by
  have hmp := measure_preserving_normTranslate μ hμ z
  refine ⟨?_, ?_, ?_⟩
  · have h1 := measurable_normTranslate_closed0 z (bigAnn C) hL₀
    rwa [shiftSet_bigAnn] at h1
  · have he : Objects.Producer.normTranslate z ⁻¹' L₀ \ Objects.Producer.centreTarget Target z =
        Objects.Producer.normTranslate z ⁻¹' (L₀ \ Target) := rfl
    rw [he]
    exact hmp.quasiMeasurePreserving.preimage_null hnull
  · exact hmp.measure_preimage (fieldSigmaClosed0_le_borel _ _ hL₀).nullMeasurableSet

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
