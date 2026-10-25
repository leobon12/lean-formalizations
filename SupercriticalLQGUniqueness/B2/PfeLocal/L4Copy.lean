import SupercriticalLQGUniqueness.B2.PfeLocal.L4Chain
import LQGMetric.Prob.CondCopies
import LQGMetric.Field.StandardBorelRange

 











set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeLocal

variable {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']

 
def l4Copy (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : Measurable h') : Measure (Ω' × Ω') :=
  condCopyMeasure id h' P' hh'

instance (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hh' : Measurable h') :
    IsProbabilityMeasure (l4Copy P' h' hh') := by
  unfold l4Copy; infer_instance

theorem l4Copy_fst (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : Measurable h') : (l4Copy P' h' hh').map Prod.fst = P' :=
  condCopyMeasure_fst hh'

theorem l4Copy_snd (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : Measurable h') : (l4Copy P' h' hh').map Prod.snd = P' := by
  have h := condCopyMeasure_map_snd (μ := P') (Y := id) hh' measurable_id
  have h2 := congrArg (fun ν : Measure (DistC × Ω') => ν.map Prod.snd) h
  rw [Measure.map_map measurable_snd (show Measurable fun p : Ω' × Ω' => (h' p.1, p.2) from
      (hh'.comp measurable_fst).prodMk measurable_snd),
    Measure.map_map measurable_snd (show Measurable fun ω : Ω' => (h' ω, id ω) from
      hh'.prodMk measurable_id)] at h2
  simp only [Function.comp_def, id_eq] at h2
  rw [show (fun x : Ω' => x) = id from rfl, Measure.map_id] at h2
  exact h2

 
theorem l4Copy_same_field (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : Measurable h') : ∀ᵐ p ∂(l4Copy P' h' hh'), h' p.2 = h' p.1 := by
  have hdiag : MeasurableSet {q : DistC × Ω' | h' q.2 = q.1} :=
    measurableSet_eq_fun (hh'.comp measurable_snd) measurable_fst
  have h := condCopyMeasure_map_snd (μ := P') (Y := id) hh' measurable_id
  have hm : Measurable fun p : Ω' × Ω' => (h' p.1, p.2) :=
    (hh'.comp measurable_fst).prodMk measurable_snd
  have hsrc : ∀ᵐ q ∂(P'.map fun ω => (h' ω, id ω)), h' q.2 = q.1 := by
    rw [ae_map_iff (hh'.prodMk measurable_id).aemeasurable hdiag]
    exact Eventually.of_forall fun ω => rfl
  rw [← h, ae_map_iff hm.aemeasurable hdiag] at hsrc
  exact hsrc

 
theorem l4Copy_fst_measure (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : Measurable h') {A : Set Ω'} (hA : MeasurableSet A) :
    l4Copy P' h' hh' (Prod.fst ⁻¹' A) = P' A := by
  rw [← Measure.map_apply measurable_fst hA, l4Copy_fst]

theorem l4Copy_snd_measure (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : Measurable h') {A : Set Ω'} (hA : MeasurableSet A) :
    l4Copy P' h' hh' (Prod.snd ⁻¹' A) = P' A := by
  rw [← Measure.map_apply measurable_snd hA, l4Copy_snd]

theorem l4Copy_ae_fst (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : Measurable h') {q : Ω' → Prop} (hq : ∀ᵐ ω ∂P', q ω) :
    ∀ᵐ p ∂(l4Copy P' h' hh'), q p.1 := by
  have : ∀ᵐ ω ∂(l4Copy P' h' hh').map Prod.fst, q ω := by rw [l4Copy_fst]; exact hq
  exact ae_of_ae_map measurable_fst.aemeasurable this

theorem l4Copy_ae_snd (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC)
    (hh' : Measurable h') {q : Ω' → Prop} (hq : ∀ᵐ ω ∂P', q ω) :
    ∀ᵐ p ∂(l4Copy P' h' hh'), q p.2 := by
  have : ∀ᵐ ω ∂(l4Copy P' h' hh').map Prod.snd, q ω := by rw [l4Copy_snd]; exact hq
  exact ae_of_ae_map measurable_snd.aemeasurable this

end SupercriticalLQGUniqueness.B2.PfeLocal
