import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Regularity




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

open LQGMetric (DistC TestC addConst addFun ofCont)

 

 
def normTranslate (z : ℂ) (u : DistC) : DistC :=
  addConst (translateDist z u) (-(LQGMetric.circleAvg u 1 z))

 

theorem normTranslate_addConst {z : ℂ} {u : DistC} (hu : CircReg u oneR z) (c : ℝ) :
    normTranslate z (addConst u c) = normTranslate z u := by
  obtain ⟨a, ha⟩ := hu
  have h1 : LQGMetric.circleAvg u 1 z = a := by
    have := circleAvg_eq_of_isCircleAverage ha
    rwa [oneR_coe] at this
  have h2 : LQGMetric.circleAvg (addConst u c) 1 z = a + c := by
    have := circleAvg_eq_of_isCircleAverage (isCircleAverage_addConst ha c)
    rwa [oneR_coe] at this
  rw [normTranslate, normTranslate, translateDist_addConst, h1, h2, addConst_addConst]
  congr 1
  ring

 

 

def LocalGood (ξ : ℝ) (D D' : DistC → LSCMetric) (Wc : Set ℂ) (Cc : Set (Set.Ioi (0 : ℝ) × ℂ))
    (u : DistC) : Prop :=
  MetricReg ξ D u ∧ MetricReg ξ D' u ∧
    (∀ w ∈ Wc, WeylReg ξ D (translateDist w u) ∧ WeylReg ξ D' (translateDist w u) ∧
      TransReg D w u ∧ TransReg D' w u) ∧
    (∀ p ∈ Cc, CircReg u p.1 p.2)

 
theorem LocalGood.addConst {ξ : ℝ} {D D' : DistC → LSCMetric} {Wc : Set ℂ}
    {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} {u : DistC} (h : LocalGood ξ D D' Wc Cc u) (c : ℝ) :
    LocalGood ξ D D' Wc Cc (addConst u c) := by
  obtain ⟨hD, hD', hW, hC⟩ := h
  refine ⟨hD.addConst c, hD'.addConst c, fun w hw => ?_, fun p hp => (hC p hp).addConst c⟩
  obtain ⟨h1, h2, h3, h4⟩ := hW w hw
  rw [translateDist_addConst]
  exact ⟨h1.addConst c, h2.addConst c, h3.addConst hD.1 h1 c, h4.addConst hD'.1 h2 c⟩

 

theorem ae_localGood {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D D' : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hQ : 0 < Q) {Wc : Set ℂ} (hWc : Wc.Countable) {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)}
    (hCc : Cc.Countable) : ∀ᵐ u ∂(P.map h), LocalGood (ξ : ℝ) D D' Wc Cc u := by
  have hW : ∀ᵐ u ∂(P.map h), ∀ w ∈ Wc, WeylReg (ξ : ℝ) D (translateDist w u) ∧
      WeylReg (ξ : ℝ) D' (translateDist w u) ∧ TransReg D w u ∧ TransReg D' w u := by
    rw [ae_ball_iff hWc]
    intro w _
    filter_upwards [ae_weylReg_translate hD hh w, ae_weylReg_translate hD' hh w,
      ae_transReg hD hh w, ae_transReg hD' hh w] with u h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hC : ∀ᵐ u ∂(P.map h), ∀ p ∈ Cc, CircReg u p.1 p.2 := by
    rw [ae_ball_iff hCc]
    intro p _
    exact ae_circReg hh p.1 p.2
  filter_upwards [ae_metricReg hD hQ hh, ae_metricReg hD' hQ hh, hW, hC] with u h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

 

 

theorem tlc_metric {ξ : ℝ} {D D' : DistC → LSCMetric} {Wc : Set ℂ}
    {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} {u : DistC} (h : LocalGood ξ D D' Wc Cc u) {z : ℂ}
    (hz : z ∈ Wc) (a b : ℂ) :
    D (normTranslate z u) (a, b) =
      ENNReal.ofReal (Real.exp (ξ * -(LQGMetric.circleAvg u 1 z))) * D u (a + z, b + z) := by
  obtain ⟨h1, -, h3, -⟩ := h.2.2.1 z hz
  rw [normTranslate, h1.scale, h3 a b]

 
theorem tlc_metric' {ξ : ℝ} {D D' : DistC → LSCMetric} {Wc : Set ℂ}
    {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} {u : DistC} (h : LocalGood ξ D D' Wc Cc u) {z : ℂ}
    (hz : z ∈ Wc) (a b : ℂ) :
    D' (normTranslate z u) (a, b) =
      ENNReal.ofReal (Real.exp (ξ * -(LQGMetric.circleAvg u 1 z))) * D' u (a + z, b + z) := by
  obtain ⟨-, h2, -, h4⟩ := h.2.2.1 z hz
  rw [normTranslate, h2.scale, h4 a b]

 

 
def centreTarget (Target : Set DistC) (z : ℂ) : Set DistC := {u | normTranslate z u ∈ Target}

theorem mem_centreTarget (Target : Set DistC) (z : ℂ) (u : DistC) :
    u ∈ centreTarget Target z ↔ normTranslate z u ∈ Target := Iff.rfl

theorem centreTarget_sat {ξ : ℝ} {D D' : DistC → LSCMetric} {Wc : Set ℂ}
    {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)} {Target : Set DistC} {z : ℂ} (hz : (oneR, z) ∈ Cc)
    (u : DistC) (c : ℝ) (hu : LocalGood ξ D D' Wc Cc u) :
    u ∈ centreTarget Target z ↔ addConst u c ∈ centreTarget Target z := by
  have hc : CircReg u oneR z := hu.2.2.2 (oneR, z) hz
  have key : normTranslate z (addConst u c) = normTranslate z u := normTranslate_addConst hc c
  rw [mem_centreTarget, mem_centreTarget, key]

 


def sectionFiveEvent {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) (ξ : ℝ)
    (D D' : DistC → LSCMetric) (Wc : Set ℂ) (Cc : Set (Set.Ioi (0 : ℝ) × ℂ))
    (Target : Set DistC) (z : ℂ) (L : Set DistC) : Set DistC :=
  producerEvent (P.map h) L (badSet (LocalGood ξ D D' Wc Cc) L (centreTarget Target z))

 




theorem sectionFiveEvent_v2 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D D' : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hQ : 0 < Q) {Wc : Set ℂ} (hWc : Wc.Countable) {Cc : Set (Set.Ioi (0 : ℝ) × ℂ)}
    (hCc : Cc.Countable) {z : ℂ} (hz : (oneR, z) ∈ Cc) (Target : Set DistC) {K : Set ℂ}
    {L : Set DistC}
    (hL : @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) L)
    (hLS : (P.map h) (L \ centreTarget Target z) = 0) (pbar : ℝ)
    (hprob : ENNReal.ofReal pbar ≤ (P.map h) L) :
    MeasurableSet (sectionFiveEvent P h (ξ : ℝ) D D' Wc Cc Target z L) ∧
      (∀ u c, u ∈ sectionFiveEvent P h (ξ : ℝ) D D' Wc Cc Target z L ↔
        addConst u c ∈ sectionFiveEvent P h (ξ : ℝ) D D' Wc Cc Target z L) ∧
      (∃ E₀ : Set DistC,
        @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) E₀ ∧
        sectionFiveEvent P h (ξ : ℝ) D D' Wc Cc Target z L =ᵐ[P.map h] E₀) ∧
      ENNReal.ofReal pbar ≤ P (h ⁻¹' sectionFiveEvent P h (ξ : ℝ) D D' Wc Cc Target z L) ∧
      sectionFiveEvent P h (ξ : ℝ) D D' Wc Cc Target z L ⊆ centreTarget Target z ∧
      (∀ u ∈ sectionFiveEvent P h (ξ : ℝ) D D' Wc Cc Target z L,
        LocalGood (ξ : ℝ) D D' Wc Cc u) := by
  have hgood := ae_localGood hh hD hD' hQ hWc hCc
  obtain ⟨hm, hc, hloc, hP, hsub, hreg⟩ :=
    fieldEvent_v2 (Good := LocalGood (ξ : ℝ) D D' Wc Cc) hh (fun u c hu => hu.addConst c) hgood hL
      (fun u c hu => centreTarget_sat hz u c hu) hLS
  refine ⟨hm, hc, hloc, ?_, hsub, hreg⟩
  have hLm : MeasurableSet L := Objects.ProducerField.fieldSigmaClosed0_id_le K L hL
  change ENNReal.ofReal pbar ≤ P (h ⁻¹' producerEvent (P.map h) L
    (badSet (LocalGood (ξ : ℝ) D D' Wc Cc) L (centreTarget Target z)))
  rw [hP, ← Measure.map_apply hh.1.measurable hLm]
  exact hprob

 

 

def producerEventN (μ : Measure DistC) (Good : DistC → Prop) (Target : Set DistC) (z : ℂ)
    (L : Set DistC) : Set DistC :=
  producerEvent μ L (badSet Good L (centreTarget Target z))

 


theorem producerEventN_constant (μ : Measure DistC) (Good : DistC → Prop) (Target : Set DistC)
    (z : ℂ) (L : Set DistC) (u : DistC) (c : ℝ) :
    u ∈ producerEventN μ Good Target z L ↔ addConst u c ∈ producerEventN μ Good Target z L :=
  producerEvent_constant μ L _ u c

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
