import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.SetGeoHit
import SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics.SetGeoExists




 





set_option autoImplicit false
noncomputable section
open Set MeasureTheory unitInterval
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics

 

def BadSetGeodesic (d : LSCMetric) (K₁ K₂ U V : Set ℂ) : Prop :=
  ∃ P : ℝ → ℂ, ∃ T : ℝ, EndSaving.FiniteEvents.SetGeodesic d K₁ K₂ P T ∧
    (∀ t ∈ Icc 0 T, P t ∉ U) ∧
    ∃ Q : ℝ → ℂ, ∃ S : ℝ, EndSaving.FiniteEvents.SetGeodesic d K₁ K₂ Q S ∧
      ∃ t ∈ Icc 0 S, Q t ∈ V

 
def BadSetGeoCode (d : LSCMetric) (K₁ K₂ U V : Set ℂ) : Prop :=
  ∃ w₁ w₂ : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
    Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (d, w₁) ∧
    Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (d, w₂) ∧
    (∀ q : unitInterval, w₁.1 q ∉ U) ∧
    ∃ q : unitInterval, w₂.1 q ∈ V

private theorem hit_iff_scaled_code
    (P : ℝ → ℂ) (T : ℝ) (R : Measurability.GeodesicCodes.Path)
    (hT : 0 ≤ T)
    (hscaled : ∀ q : unitInterval, R q = P (T * (q : ℝ)))
    (O : Set ℂ) :
    (∃ t ∈ Icc 0 T, P t ∈ O) ↔
      ∃ q : unitInterval, R q ∈ O := by
  constructor
  · rintro ⟨t, ht, hPt⟩
    rcases hT.eq_or_lt with hzero | hpos
    · have ht0 : t = 0 := le_antisymm (hzero ▸ ht.2) ht.1
      refine ⟨0, ?_⟩
      simpa only [hscaled, Set.Icc.coe_zero, mul_zero, ht0] using hPt
    · let q : unitInterval := ⟨t / T,
        ⟨div_nonneg ht.1 hT, (div_le_one hpos).mpr ht.2⟩⟩
      refine ⟨q, ?_⟩
      have htime : T * (q : ℝ) = t := by
        change T * (t / T) = t
        field_simp
      rw [← htime] at hPt
      rwa [hscaled]
  · rintro ⟨q, hRq⟩
    refine ⟨T * (q : ℝ), ?_, ?_⟩
    · exact ⟨mul_nonneg hT q.2.1, mul_le_of_le_one_right hT q.2.2⟩
    · simpa only [hscaled q] using hRq

 

theorem badSetGeodesic_iff_code (d : LSCMetric) (K₁ K₂ U V : Set ℂ)
    (hforget : Continuous (Measurability.SetGeodesicCodes.euclidForget d)) :
    BadSetGeodesic d K₁ K₂ U V ↔ BadSetGeoCode d K₁ K₂ U V := by
  constructor
  · rintro ⟨P, T, hP, hAvoid, Q, S, hQ, hHit⟩
    obtain ⟨R, hR, hscaledR⟩ :=
      Measurability.SetGeodesicCodes.setGeodesic_scaled_candidate d K₁ K₂ P T hforget hP
    obtain ⟨R', hR', hscaledR'⟩ :=
      Measurability.SetGeodesicCodes.setGeodesic_scaled_candidate d K₁ K₂ Q S hforget hQ
    refine ⟨(R, (P 0, P T)), (R', (Q 0, Q S)), hR, hR', ?_, ?_⟩
    · intro q hq
      exact hAvoid _ (by
        exact ⟨mul_nonneg hP.1.1.1 q.2.1,
          mul_le_of_le_one_right hP.1.1.1 q.2.2⟩)
        (by rwa [hscaledR] at hq)
    · exact (hit_iff_scaled_code Q S R' hQ.1.1.1 hscaledR' V).1 hHit
  · rintro ⟨⟨R, uv⟩, ⟨R', uv'⟩, hR, hR', hAvoid, hHit⟩
    obtain ⟨P, T, hP, hscaledR⟩ :=
      Measurability.SetGeodesicCodes.setGeoCandidate_has_scaled_source d K₁ K₂ R uv.1 uv.2 hR
    obtain ⟨Q, S, hQ, hscaledR'⟩ :=
      Measurability.SetGeodesicCodes.setGeoCandidate_has_scaled_source d K₁ K₂ R' uv'.1 uv'.2 hR'
    refine ⟨P, T, hP, ?_, Q, S, hQ, ?_⟩
    · intro t ht hPt
      obtain ⟨q, hq⟩ :=
        (hit_iff_scaled_code P T R hP.1.1.1
          (fun q => (hscaledR q).symm) U).1 ⟨t, ht, hPt⟩
      exact hAvoid q hq
    · exact (hit_iff_scaled_code Q S R' hQ.1.1.1
        (fun q => (hscaledR' q).symm) V).2 hHit

 

theorem badSetGeoCode_um (D : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (K₁ K₂ U V : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hU : IsOpen U) (hV : IsOpen V) :
    LQGMetric.UMeasurableSet
      {g : LQGMetric.DistC |
        BadSetGeoCode (D g) K₁ K₂ U V} := by
  let W := Measurability.GeodesicCodes.Path × (ℂ × ℂ)
  have hStd : StandardBorelSpace (W × W) :=
    @StandardBorelSpace.prod W (inferInstance) W (inferInstance)
      (inferInstance) (inferInstance)
  let C : Set (LSCMetric × (W × W)) :=
    {p | Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (p.1, p.2.1) ∧
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (p.1, p.2.2) ∧
      (∀ q : unitInterval, p.2.1.1 q ∉ U) ∧
      ∃ q : unitInterval, p.2.2.1 q ∈ V}
  have hCandidate : MeasurableSet
      {p : LSCMetric × W | Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ p} :=
    Measurability.ClauseEvents.setGeoCandidate_measurable K₁ K₂ hK₁ hK₂
  have hleft : Measurable (fun p : LSCMetric × (W × W) => (p.1, p.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hright : Measurable (fun p : LSCMetric × (W × W) => (p.1, p.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hPathLeft : Measurable (fun p : LSCMetric × (W × W) => p.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hPathRight : Measurable (fun p : LSCMetric × (W × W) => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hAvoid : MeasurableSet
      {p : LSCMetric × (W × W) | ∀ q : unitInterval, p.2.1.1 q ∉ U} := by
    convert ((Measurability.SetGeodesicCodes.setGeoCode_hit_open U hU).measurableSet.preimage hPathLeft).compl using 1
    ext p
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_exists]
  have hHit : MeasurableSet
      {p : LSCMetric × (W × W) | ∃ q : unitInterval, p.2.2.1 q ∈ V} :=
    (Measurability.SetGeodesicCodes.setGeoCode_hit_open V hV).measurableSet.preimage hPathRight
  have hC : MeasurableSet C := by
    convert (((hCandidate.preimage hleft).inter (hCandidate.preimage hright)).inter hAvoid).inter hHit using 1
    ext p
    simp only [C, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hProj : LQGMetric.UMeasurableSet
      {g : LQGMetric.DistC | ∃ w : W × W, (D g, w) ∈ C} :=
    @Measurability.GeodesicCodes.witnessProjection_um (W × W) (inferInstance) hStd D hD C hC
  convert hProj using 1
  ext g
  simp only [BadSetGeoCode, C, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w₁, w₂, h₁, h₂, hA, hH⟩
    exact ⟨(w₁, w₂), h₁, h₂, hA, hH⟩
  · rintro ⟨⟨w₁, w₂⟩, h₁, h₂, hA, hH⟩
    exact ⟨w₁, w₂, h₁, h₂, hA, hH⟩

 

theorem ae_badSetGeodesic_iff_code_all_shifts
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : LQGMetric.DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h μ) :
    ∀ᵐ ω ∂μ,
      (∀ K₁ K₂ U V : Set ℂ,
        BadSetGeodesic (D (h ω)) K₁ K₂ U V ↔
          BadSetGeoCode (D (h ω)) K₁ K₂ U V) ∧
      (∀ φ : LQGMetric.TestC, ∀ K₁ K₂ U V : Set ℂ,
        BadSetGeodesic
          (D (LQGMetric.GM.subTest (h ω) φ)) K₁ K₂ U V ↔
        BadSetGeoCode
          (D (LQGMetric.GM.subTest (h ω) φ)) K₁ K₂ U V) := by
  filter_upwards [Toolkit.WeylShift.ae_common_weyl_sample hD μ h hh,
    Toolkit.WeylShift.ae_all_shift_curves hD μ h hh] with ω hbase hshift
  constructor
  · intro K₁ K₂ U V
    exact badSetGeodesic_iff_code (D (h ω)) K₁ K₂ U V hbase.1
  · intro φ K₁ K₂ U V
    have hcont := (hshift (-LQGMetric.testCont φ)).1
    change Continuous
      (Measurability.SetGeodesicCodes.euclidForget (D (LQGMetric.GM.subTest (h ω) φ))) at hcont
    exact badSetGeodesic_iff_code
      (D (LQGMetric.GM.subTest (h ω) φ)) K₁ K₂ U V hcont

 

theorem badSetGeodesic_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : LQGMetric.DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (K₁ K₂ U V : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hU : IsOpen U) (hV : IsOpen V) :
    NullMeasurableSet
      {g : LQGMetric.DistC | BadSetGeodesic (D g) K₁ K₂ U V}
      (μ.map h) := by
  have hcode : NullMeasurableSet
      {g : LQGMetric.DistC | BadSetGeoCode (D g) K₁ K₂ U V}
      (μ.map h) :=
    (badSetGeoCode_um D hD.1 K₁ K₂ U V hK₁ hK₂ hU hV).nullMeasurableSet (μ.map h)
  have hcanonical : IsNormalizedWholePlaneGFF
      (id : LQGMetric.DistC → LQGMetric.DistC) (μ.map h) :=
    Measurability.SetGeodesicCodes.normalizedGFF_id_map μ h hh
  have hae :
      {g : LQGMetric.DistC | BadSetGeodesic (D g) K₁ K₂ U V} =ᵐ[μ.map h]
      {g : LQGMetric.DistC | BadSetGeoCode (D g) K₁ K₂ U V} := by
    filter_upwards [ae_badSetGeodesic_iff_code_all_shifts
      hD (μ.map h) id hcanonical] with g hg
    exact propext (hg.1 K₁ K₂ U V)
  exact hcode.congr hae.symm

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics
