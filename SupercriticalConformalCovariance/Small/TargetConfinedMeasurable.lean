import SupercriticalConformalCovariance.Small.ConfinedRegularity
import SupercriticalConformalCovariance.Small.AmbientMetricLift
import SupercriticalConformalCovariance.Lemma31.LscMeas
import LQGMetric.Meas.UM

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set TopologicalSpace MeasureTheory Classical
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness

private theorem lsc_extend_closed_embedding
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {e : A → B} (he : Topology.IsClosedEmbedding e) {f : A → EReal}
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun b : B => ⨅ a : A, if e a = b then f a else ⊤) := by
  let F : B → EReal := fun b => ⨅ a : A, if e a = b then f a else ⊤
  have hon : ∀ a, F (e a) = f a := by
    intro a
    apply le_antisymm
    · exact iInf_le_of_le a (by simp [F])
    · refine le_iInf fun a' => ?_
      by_cases h : e a' = e a
      · have heq := he.injective h
        subst a'
        simp [F]
      · simp [h]
  have hoff : ∀ b, b ∉ range e → F b = ⊤ := by
    intro b hb
    simp only [F]
    have h : ∀ a : A, e a ≠ b := fun a ha => hb ⟨a, ha⟩
    simp [h]
  apply lowerSemicontinuous_iff_isClosed_preimage.2
  intro t
  by_cases ht : t = ⊤
  · subst t
    simp
  have hpre : F ⁻¹' Iic t = e '' (f ⁻¹' Iic t) := by
    ext b
    constructor
    · intro hb
      by_cases hr : b ∈ range e
      · rcases hr with ⟨a, rfl⟩
        exact ⟨a, by simpa [hon a] using hb, rfl⟩
      · have htop := hoff b hr
        have hle : (⊤ : EReal) ≤ t := by simpa [hoff b hr] using hb
        exact (ht (top_le_iff.mp hle)).elim
    · rintro ⟨a, ha, rfl⟩
      simpa [hon] using ha
  rw [hpre]
  exact he.isClosedMap _ (hf.isClosed_preimage t)

private def pullRaw (L K : Set ℂ) (j : C(K,L))
    (p : LSCMetric × (ℂ × ℂ)) : EReal :=
  ⨅ a : LSCMetric × (K × K),
    if (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) = p then
      ((a.1.internal L (j a.2.1, j a.2.2) : ℝ≥0∞) : EReal) else ⊤

private theorem pullRaw_lsc (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K,L)) :
    LowerSemicontinuous (pullRaw L K j) := by
  let e : LSCMetric × (K × K) → LSCMetric × (ℂ × ℂ) :=
    fun a => (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ)))
  have he : Topology.IsClosedEmbedding e := by
    change Topology.IsClosedEmbedding
      (Prod.map id (Prod.map (Subtype.val : K → ℂ) (Subtype.val : K → ℂ)))
    exact Topology.IsClosedEmbedding.id.prodMap
      (hK.isClosed.isClosedEmbedding_subtypeVal.prodMap
        hK.isClosed.isClosedEmbedding_subtypeVal)
  have hc : Continuous (fun a : LSCMetric × (K × K) =>
      (a.1, (j a.2.1, j a.2.2))) :=
    continuous_fst.prodMk
      (((j.continuous.comp (continuous_fst.comp continuous_snd))).prodMk
        (j.continuous.comp (continuous_snd.comp continuous_snd)))
  have hG : LowerSemicontinuous (fun p : LSCMetric × (L × L) =>
      ((p.1.internal L p.2 : ℝ≥0∞) : EReal)) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      (SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.internal_compact_joint_lsc hL)
      EReal.coe_ennreal_strictMono.monotone
  have hf : LowerSemicontinuous (fun a : LSCMetric × (K × K) =>
      ((a.1.internal L (j a.2.1, j a.2.2) : ℝ≥0∞) : EReal)) := by
    change LowerSemicontinuous
      ((fun p : LSCMetric × (L × L) =>
        ((p.1.internal L p.2 : ℝ≥0∞) : EReal)) ∘
        fun a : LSCMetric × (K × K) => (a.1, (j a.2.1, j a.2.2)))
    exact hG.comp hc
  convert lsc_extend_closed_embedding he hf using 1
  funext p
  simp only [pullRaw, e]
  refine iInf_congr fun a => ?_
  by_cases h : (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) = p <;> simp [h]

private theorem pullRaw_on (L K : Set ℂ) (j : C(K,L))
    (D : LSCMetric) (x y : K) :
    pullRaw L K j (D, ((x : ℂ), (y : ℂ))) =
      ((D.internal L (j x, j y) : ℝ≥0∞) : EReal) := by
  have he : Function.Injective
      (fun a : LSCMetric × (K × K) =>
        (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ)))) := by
    intro a b hab
    have h₁ : a.1 = b.1 := congrArg (fun p : LSCMetric × (ℂ × ℂ) => p.1) hab
    have h₂ : ((a.2.1 : ℂ), (a.2.2 : ℂ)) =
        ((b.2.1 : ℂ), (b.2.2 : ℂ)) :=
      congrArg (fun p : LSCMetric × (ℂ × ℂ) => p.2) hab
    apply Prod.ext
    · exact h₁
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst h₂
      · apply Subtype.ext
        exact congrArg Prod.snd h₂
  unfold pullRaw
  apply le_antisymm
  · exact iInf_le_of_le (D, (x,y)) (by simp)
  · refine le_iInf fun a => ?_
    by_cases ha : (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) =
        (D, ((x : ℂ), (y : ℂ)))
    · have hae : a = (D,(x,y)) := he ha
      subst a
      simp
    · simp [ha]

private theorem pullRaw_off (L K : Set ℂ) (j : C(K,L))
    (D : LSCMetric) (x y : ℂ)
    (h : ¬(x ∈ K ∧ y ∈ K)) :
    pullRaw L K j (D,(x,y)) = ⊤ := by
  unfold pullRaw
  have he : ∀ a : LSCMetric × (K × K),
      (a.1, ((a.2.1 : ℂ), (a.2.2 : ℂ))) ≠ (D,(x,y)) := by
    intro a ha
    have hp := congrArg (fun p : LSCMetric × (ℂ × ℂ) => p.2) ha
    have hx : (a.2.1 : ℂ) = x := congrArg Prod.fst hp
    have hy : (a.2.2 : ℂ) = y := congrArg Prod.snd hp
    exact h ⟨hx ▸ a.2.1.2, hy ▸ a.2.2.2⟩
  simp [he]

private theorem pullRaw_nonneg (L K : Set ℂ) (j : C(K,L))
    (p : LSCMetric × (ℂ × ℂ)) :
    (0 : EReal) ≤ pullRaw L K j p := by
  unfold pullRaw
  refine le_iInf fun a => ?_
  split_ifs
  · exact EReal.coe_ennreal_nonneg _
  · exact le_top

private theorem pullCorrected_joint_lsc (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K,L)) :
    LowerSemicontinuous (fun p : LSCMetric × (ℂ × ℂ) =>
      if p.2.1 = p.2.2 then (0 : EReal) else pullRaw L K j p) := by
  have hraw := pullRaw_lsc L K hK hL j
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hraw ⊢
  intro a
  let O : Set (LSCMetric × (ℂ × ℂ)) := {p | p.2.1 ≠ p.2.2}
  have hO : IsOpen O :=
    (isClosed_eq (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).isOpen_compl
  by_cases ha : a < (0 : EReal)
  · have hset : (fun p : LSCMetric × (ℂ × ℂ) =>
        if p.2.1 = p.2.2 then (0 : EReal) else pullRaw L K j p) ⁻¹' Ioi a =
        Set.univ := by
      ext p
      by_cases hp : p.2.1 = p.2.2
      · simp [hp, ha]
      · simp [hp, lt_of_lt_of_le ha (pullRaw_nonneg L K j p)]
    rw [hset]
    exact isOpen_univ
  · have hset : (fun p : LSCMetric × (ℂ × ℂ) =>
        if p.2.1 = p.2.2 then (0 : EReal) else pullRaw L K j p) ⁻¹' Ioi a =
        pullRaw L K j ⁻¹' Ioi a ∩ O := by
      ext p
      by_cases hp : p.2.1 = p.2.2 <;> simp [hp, O, ha]
    rw [hset]
    exact (hraw a).inter hO

def targetConfSection (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K,L)) (D : LSCMetric) : LSCFun :=
  SupercriticalConformalCovariance.Lemma31.lscSection
    (fun D q => if q.1 = q.2 then (0 : EReal) else pullRaw L K j (D,q))
    (pullCorrected_joint_lsc L K hK hL j) D

theorem targetConfSection_eq (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K,L)) (hj : Function.Injective j)
    (D : LSCMetric) :
    targetConfSection L K hK hL j D =
      (confPullCompact D L K hK hL j hj).toLSCFun := by
  apply Subtype.ext
  funext p
  change (if p.1 = p.2 then (0 : EReal) else pullRaw L K j (D,p)) =
    ((extendMetric K (pullInner D L K j) p : ℝ≥0∞) : EReal)
  by_cases hxy : p.1 = p.2
  · simp [hxy, extendMetric]
  · by_cases hp : p.1 ∈ K ∧ p.2 ∈ K
    · rcases hp with ⟨hx,hy⟩
      have hraw : pullRaw L K j (D,p) =
          ((D.internal L (j ⟨p.1,hx⟩, j ⟨p.2,hy⟩) : ℝ≥0∞) : EReal) := by
        simpa only using pullRaw_on L K j D ⟨p.1,hx⟩ ⟨p.2,hy⟩
      simp [hxy, extendMetric, hx, hy, pullInner, hraw]
    · have hraw := pullRaw_off L K j D p.1 p.2 hp
      simp [hxy, extendMetric, hp, hraw]

theorem measurable_confPullCompact [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (L K : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K,L)) (hj : Function.Injective j) :
    Measurable fun D : LSCMetric =>
      (confPullCompact D L K hK hL j hj).toLSCFun := by
  have := SupercriticalLQGUniqueness.B2.LscTop.borelSpace_LSCMetric
  have hm : Measurable (targetConfSection L K hK hL j) := by
    unfold targetConfSection
    exact SupercriticalConformalCovariance.Lemma31.measurable_lscSection _ _
  have heq : (fun D : LSCMetric =>
      (confPullCompact D L K hK hL j hj).toLSCFun) =
      targetConfSection L K hK hL j := by
    funext D
    exact (targetConfSection_eq L K hK hL j hj D).symm
  rw [heq]
  exact hm

local instance targetMeasurableSpaceLSCFun : MeasurableSpace LSCFun := borel LSCFun
local instance targetBorelSpaceLSCFun : BorelSpace LSCFun := ⟨rfl⟩

theorem um_target_confined_image
    (L K : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K,L)) (hj : Function.Injective j) :
    LQGMetric.UMeasurableSet
      (Set.range (fun F : LSCFun =>
        (confPullCompact (ambientMetricLift F) L K hK hL j hj).toLSCFun)) := by
  have hf : Measurable (fun F : LSCFun =>
      (confPullCompact (ambientMetricLift F) L K hK hL j hj).toLSCFun) :=
    (measurable_confPullCompact L K hK hL j hj).comp ambientMetricLift_measurable
  have hu := LQGMetric.UMeasurableSet.image hf
    (s := (Set.univ : Set LSCFun)) MeasurableSet.univ
  simpa only [Set.image_univ] using hu

theorem target_conf_mem_um_image
    (D : LSCMetric) (L K : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K,L)) (hj : Function.Injective j) :
    (confPullCompact D L K hK hL j hj).toLSCFun ∈
      Set.range (fun F : LSCFun =>
        (confPullCompact (ambientMetricLift F) L K hK hL j hj).toLSCFun) := by
  refine ⟨D.toLSCFun, ?_⟩
  simp only [ambientMetricLift_eq]

theorem target_conf_image_geometry
    (L K : Set ℂ) (hK : IsCompact K) (hL : IsCompact L)
    (j : C(K,L)) (hj : Function.Injective j)
    (jInv : C(L,K)) (hjInv : ∀ y : L, j (jInv y) = y)
    (F : LSCFun)
    (hF : F ∈ Set.range (fun G : LSCFun =>
      (confPullCompact (ambientMetricLift G) L K hK hL j hj).toLSCFun)) :
    (ambientMetricLift F).IsLengthSpace ∧
      (∀ (P : ℝ → ℂ) (a b : ℝ), (ambientMetricLift F).IsCurve P a b →
        (ambientMetricLift F).len P a b < ⊤ → ContinuousOn P (Icc a b)) := by
  obtain ⟨G, rfl⟩ := hF
  rw [ambientMetricLift_eq]
  exact ⟨confPullCompact_isLengthSpace (ambientMetricLift G) L K hK hL j hj jInv hjInv,
    fun P a b hP _ =>
      confPullCompact_euclidean_regular_any (ambientMetricLift G) L K hK hL j hj P a b hP⟩

end SupercriticalConformalCovariance.Small
