import SupercriticalLQGUniqueness.Uniqueness.Objects.ProducerField.FieldEvent
import LQGMetric.Papers.GM.S6.GeodSelN
import LQGMetric.Field.CircleAvgGauss
import LQGMetric.Field.MeasurableAvg
import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent




 





















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

open LQGMetric (DistC TestC addConst)
open LQGMetric.GM (normPsi psiOne normPsi_addConst measurable_normPsi)

 

theorem addConst_addConst (u : DistC) (a b : ℝ) :
    addConst (addConst u a) b = addConst u (a + b) :=
  LQGMetric.GFFLaw.addConst_addConst u a b

theorem addConst_zero (u : DistC) : addConst u 0 = u :=
  LQGMetric.GFFLaw.addConst_zero' u

 
theorem addConst_normPsi (u : DistC) : addConst (normPsi u) (u psiOne) = u := by
  rw [normPsi, addConst_addConst, neg_add_cancel, addConst_zero]

 
theorem sat_iff {p : DistC → Prop} (hsat : ∀ u c, p u → p (addConst u c)) (u : DistC) (c : ℝ) :
    p u ↔ p (addConst u c) := by
  refine ⟨hsat u c, fun h => ?_⟩
  have := hsat (addConst u c) (-c) h
  rwa [addConst_addConst, add_neg_cancel, addConst_zero] at this

 

 

def producerEvent (μ : Measure DistC) (L Bad : Set DistC) : Set DistC :=
  normPsi ⁻¹' (L \ toMeasurable (μ.map normPsi) Bad)

theorem measurableSet_producerEvent (μ : Measure DistC) {L : Set DistC} (hL : MeasurableSet L)
    (Bad : Set DistC) : MeasurableSet (producerEvent μ L Bad) :=
  (hL.diff (measurableSet_toMeasurable _ _)).preimage measurable_normPsi

 


theorem producerEvent_constant (μ : Measure DistC) (L Bad : Set DistC) (u : DistC) (c : ℝ) :
    u ∈ producerEvent μ L Bad ↔ addConst u c ∈ producerEvent μ L Bad := by
  simp only [producerEvent, mem_preimage, normPsi_addConst]

 

theorem producerEvent_subset (μ : Measure DistC) {L S Bad : Set DistC} {Good : DistC → Prop}
    (hsat : ∀ u c, Good u → Good (addConst u c))
    (hSsat : ∀ u c, Good u → (u ∈ S ↔ addConst u c ∈ S))
    (hBad : {y | ¬ Good y} ∪ (L \ S) ⊆ Bad) :
    producerEvent μ L Bad ⊆ S ∩ {u | Good u} := by
  rintro u ⟨huL, huT⟩
  have hnot : normPsi u ∉ Bad := fun h => huT (subset_toMeasurable _ _ h)
  have hgood : Good (normPsi u) := by
    by_contra hc
    exact hnot (hBad (Or.inl hc))
  have hS : normPsi u ∈ S := by
    by_contra hc
    exact hnot (hBad (Or.inr ⟨huL, hc⟩))
  have h1 := (hSsat (normPsi u) (u psiOne) hgood).1 hS
  have h2 := hsat (normPsi u) (u psiOne) hgood
  rw [addConst_normPsi] at h1 h2
  exact ⟨h1, h2⟩

 

theorem producerEvent_ae_eq (μ : Measure DistC) {L Bad : Set DistC}
    (hLsat : ∀ u c, u ∈ L ↔ addConst u c ∈ L) (hnull : (μ.map normPsi) Bad = 0) :
    producerEvent μ L Bad =ᵐ[μ] L := by
  set T := toMeasurable (μ.map normPsi) Bad with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : (μ.map normPsi) T = 0 := by rw [hT, measure_toMeasurable]; exact hnull
  have hLN : ∀ u, u ∈ L ↔ normPsi u ∈ L := by
    intro u
    have := hLsat (normPsi u) (u psiOne)
    rw [addConst_normPsi] at this
    exact this.symm
  have heq : producerEvent μ L Bad = L \ normPsi ⁻¹' T := by
    ext u
    show normPsi u ∈ L \ T ↔ u ∈ L \ normPsi ⁻¹' T
    simp only [Set.mem_sdiff, mem_preimage]
    rw [← hLN u]
  have hnullT : μ (normPsi ⁻¹' T) = 0 := by
    rw [← Measure.map_apply measurable_normPsi hTm]; exact hT0
  rw [heq]
  exact sdiff_null_ae_eq_self hnullT

 

 
def retract (y : DistC) : DistC := addConst y (-(LQGMetric.circleAvg y 1 0))

theorem measurable_retract : Measurable retract := by
  refine LQGMetric.GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [retract, LQGMetric.GFFInv.addConst_apply]
  exact (LQGMetric.GFFInv.measurable_pair φ).add
    (measurable_const.mul (LQGMetric.measurable_circleAvg_left 1 0).neg)

theorem retract_orbit (y : DistC) : ∃ c, retract y = addConst y c := ⟨_, rfl⟩

 
theorem isCircleAverage_iff_mollAvg (g : DistC) (r : Set.Ioi (0 : ℝ)) (z : ℂ) (a : ℝ) :
    IsCircleAverage g r z a ↔
      Tendsto (fun n => LQGMetric.CircleAvg.mollAvg g n z (r : ℝ)) atTop (𝓝 a) :=
  Iff.rfl

 
theorem circleAvg_eq_of_isCircleAverage {g : DistC} {r : Set.Ioi (0 : ℝ)} {z : ℂ} {a : ℝ}
    (h : IsCircleAverage g r z a) : LQGMetric.circleAvg g (r : ℝ) z = a :=
  LQGMetric.CircleAvg.circleAvg_eq_of_tendsto h

 
theorem isCircleAverage_addConst {g : DistC} {r : Set.Ioi (0 : ℝ)} {z : ℂ} {a : ℝ}
    (h : IsCircleAverage g r z a) (c : ℝ) : IsCircleAverage (addConst g c) r z (a + c) := by
  rw [isCircleAverage_iff_mollAvg] at h ⊢
  simp_rw [LQGMetric.CircleAvg.mollAvg_addConst]
  exact h.add_const c

 
theorem measurableSet_isCircleAverage (r : Set.Ioi (0 : ℝ)) (z : ℂ) (a : ℝ) :
    MeasurableSet {g : DistC | IsCircleAverage g r z a} := by
  have hf : ∀ n : ℕ, Measurable fun g : DistC => LQGMetric.CircleAvg.mollAvg g n z (r : ℝ) := by
    intro n
    have : (fun g : DistC => LQGMetric.CircleAvg.mollAvg g n z (r : ℝ)) =
        fun g : DistC => g (LQGMetric.CircleAvg.circBump n z (r : ℝ)) := by
      funext g
      exact LQGMetric.CircleAvg.circleAverage_pairing g n z r
    rw [this]
    exact LQGMetric.GFFInv.measurable_pair _
  exact measurableSet_tendsto (𝓝 a) hf

 
theorem measurableSet_exists_isCircleAverage (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    MeasurableSet {g : DistC | ∃ a, IsCircleAverage g r z a} := by
  have hf : ∀ n : ℕ, Measurable fun g : DistC => LQGMetric.CircleAvg.mollAvg g n z (r : ℝ) := by
    intro n
    have : (fun g : DistC => LQGMetric.CircleAvg.mollAvg g n z (r : ℝ)) =
        fun g : DistC => g (LQGMetric.CircleAvg.circBump n z (r : ℝ)) := by
      funext g
      exact LQGMetric.CircleAvg.circleAverage_pairing g n z r
    rw [this]
    exact LQGMetric.GFFInv.measurable_pair _
  exact measurableSet_exists_tendsto hf

 
def oneR : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩

 
theorem oneR_coe : ((oneR : Set.Ioi (0 : ℝ)) : ℝ) = 1 := rfl

theorem normPsi_eq (u : DistC) : normPsi u = addConst u (-(u psiOne)) := rfl

theorem retract_normPsi {u : DistC} (hu : IsCircleAverage u oneR 0 0) : retract (normPsi u) = u := by
  have h0 : IsCircleAverage (addConst u (-(u psiOne))) oneR 0 (0 + -(u psiOne)) :=
    isCircleAverage_addConst hu (-(u psiOne))
  have h1 : LQGMetric.circleAvg (addConst u (-(u psiOne))) ((oneR : Set.Ioi (0 : ℝ)) : ℝ) 0 =
      0 + -(u psiOne) := circleAvg_eq_of_isCircleAverage h0
  rw [oneR_coe] at h1
  rw [retract, normPsi_eq, h1, zero_add, neg_neg, addConst_addConst, neg_add_cancel,
    addConst_zero]

 
theorem ae_retract_normPsi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) : ∀ᵐ u ∂(P.map h), retract (normPsi u) = u := by
  have hmeas : MeasurableSet {g : DistC | IsCircleAverage g oneR 0 0} :=
    measurableSet_isCircleAverage oneR 0 0
  have hae : ∀ᵐ u ∂(P.map h), IsCircleAverage u oneR 0 0 :=
    (ae_map_iff hh.1.measurable.aemeasurable hmeas).2 hh.2
  filter_upwards [hae] with u hu
  exact retract_normPsi hu

 

theorem map_normPsi_null {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) {Bad : Set DistC} (hBad : (P.map h) Bad = 0)
    (hinv : ∀ y ∈ Bad, ∀ c, addConst y c ∈ Bad) : ((P.map h).map normPsi) Bad = 0 :=
  Objects.ProducerField.map_null_of_retraction (P.map h) normPsi retract measurable_normPsi measurable_retract
    (ae_retract_normPsi hh) hBad (fun y hy => by
      obtain ⟨c, hc⟩ := retract_orbit y
      rw [hc]
      exact hinv y hy c)

 

 
def badSet (Good : DistC → Prop) (L S : Set DistC) : Set DistC :=
  {y | ¬ Good y} ∪ (L \ S)

theorem badSet_inv {Good : DistC → Prop} {L S : Set DistC}
    (hsat : ∀ u c, Good u → Good (addConst u c))
    (hLsat : ∀ u c, u ∈ L ↔ addConst u c ∈ L)
    (hSsat : ∀ u c, Good u → (u ∈ S ↔ addConst u c ∈ S)) :
    ∀ y ∈ badSet Good L S, ∀ c, addConst y c ∈ badSet Good L S := by
  intro y hy c
  rcases hy with hy | ⟨hyL, hyS⟩
  · left
    intro hg
    exact hy ((sat_iff hsat y c).2 hg)
  · by_cases hg : Good y
    · right
      exact ⟨(hLsat y c).1 hyL, fun h => hyS ((hSsat y c hg).2 h)⟩
    · left
      intro hg'
      exact hg ((sat_iff hsat y c).2 hg')

 

 





theorem fieldEvent_v2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) {Good : DistC → Prop}
    (hsat : ∀ u c, Good u → Good (addConst u c)) (hgood : ∀ᵐ u ∂(P.map h), Good u)
    {K : Set ℂ} {L S : Set DistC}
    (hL : @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) L)
    (hSsat : ∀ u c, Good u → (u ∈ S ↔ addConst u c ∈ S))
    (hLS : (P.map h) (L \ S) = 0) :
    let E := producerEvent (P.map h) L (badSet Good L S)
    MeasurableSet E ∧ (∀ u c, u ∈ E ↔ addConst u c ∈ E) ∧
      (∃ E₀ : Set DistC,
        @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) E₀ ∧
        E =ᵐ[P.map h] E₀) ∧
      P (h ⁻¹' E) = P (h ⁻¹' L) ∧ E ⊆ S ∧ (∀ u ∈ E, Good u) := by
  intro E
  have hLm : MeasurableSet L := Objects.ProducerField.fieldSigmaClosed0_id_le K L hL
  have hLsat : ∀ u c, u ∈ L ↔ addConst u c ∈ L := Objects.ProducerField.mem_fieldSigmaClosed0_id_addConst hL
  have hbad0 : (P.map h) (badSet Good L S) = 0 := by
    refine measure_union_null ?_ hLS
    rwa [ae_iff] at hgood
  have hnull : ((P.map h).map normPsi) (badSet Good L S) = 0 :=
    map_normPsi_null hh hbad0 (badSet_inv hsat hLsat hSsat)
  have hEm : MeasurableSet E := measurableSet_producerEvent _ hLm _
  have hae : E =ᵐ[P.map h] L := producerEvent_ae_eq _ hLsat hnull
  have hsub : E ⊆ S ∩ {u | Good u} :=
    producerEvent_subset _ hsat hSsat (subset_refl _)
  refine ⟨hEm, producerEvent_constant _ _ _, ⟨L, hL, hae⟩, ?_, fun u hu => (hsub hu).1,
    fun u hu => (hsub hu).2⟩
  rw [← Measure.map_apply hh.1.measurable hEm, ← Measure.map_apply hh.1.measurable hLm]
  exact measure_congr hae

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
