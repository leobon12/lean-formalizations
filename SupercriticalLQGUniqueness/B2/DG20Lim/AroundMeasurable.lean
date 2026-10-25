import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoords
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundWitness
import LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

open LQGMetric

theorem RatAnnulus.isClosed_toSet (A : RatAnnulus) : IsClosed A.toSet := by
  unfold RatAnnulus.toSet RatCircle.closedDisk RatCircle.openDisk
  exact Metric.isClosed_closedBall.inter Metric.isOpen_ball.isClosed_compl

 

theorem um_aroundDist_lt_closed (A E F : Set ℂ) (hA : IsClosed A) (c : ℝ≥0∞) :
    UMeasurableSet {D : ContMetric | D.aroundDist A E F < c} := by
  let R : Set (ContMetric × C(unitInterval, ℂ)) :=
    {p | range p.2 ⊆ A ∧ LQGMetric.Disconnects (range p.2) E F ∧
      p.1.len (fun t => p.2 (LQGMetric.GM.pj t)) 0 1 < c}
  have hcar : MeasurableSet
      {p : ContMetric × C(unitInterval, ℂ) | range p.2 ⊆ A} := by
    have hclosed : IsClosed {η : C(unitInterval, ℂ) | range η ⊆ A} := by
      have heq : {η : C(unitInterval, ℂ) | range η ⊆ A} =
          ⋂ t : unitInterval, {η : C(unitInterval, ℂ) | η t ∈ A} := by
        ext η
        simp only [mem_ofPred_eq, range_subset_iff, mem_iInter]
      rw [heq]
      exact isClosed_iInter fun t =>
        hA.preimage (continuous_eval_const (F := C(unitInterval, ℂ)) t)
    exact hclosed.measurableSet.preimage measurable_snd
  have hsep : MeasurableSet
      {p : ContMetric × C(unitInterval, ℂ) | LQGMetric.Disconnects (range p.2) E F} := by
    have hc := (LQGMetric.GM.isOpen_setOf_not_disconnects E F).measurableSet.compl
    have hc' : MeasurableSet
        {η : C(unitInterval, ℂ) | LQGMetric.Disconnects (range η) E F} := by
      convert hc using 1
      ext η
      simp
    exact hc'.preimage measurable_snd
  have hlen : MeasurableSet
      {p : ContMetric × C(unitInterval, ℂ) |
        p.1.len (fun t => p.2 (LQGMetric.GM.pj t)) 0 1 < c} :=
    measurableSet_lt LQGMetric.GM.lowerSemicontinuous_lenPath.measurable measurable_const
  have hR : MeasurableSet R := hcar.inter (hsep.inter hlen)
  have hproj : UMeasurableSet
      {D : ContMetric | ∃ η : C(unitInterval, ℂ), (D, η) ∈ R} :=
    UMeasurableSet.setOf_exists hR
  convert hproj using 1
  ext D
  constructor
  · intro h
    obtain ⟨a, b, P, hab, hcont, hcar', hsep', hlen'⟩ :=
      DG20Conc.laneC_exists_around_witness_of_lt D A E F h
    obtain ⟨η, hη⟩ := (LQGMetric.GM.exists_path_iff D
      (fun I l => I ⊆ A ∧ LQGMetric.Disconnects I E F ∧ l < c)).mp
        ⟨a, b, P, hab, hcont, hcar', hsep', hlen'⟩
    exact ⟨η, hη⟩
  · rintro ⟨η, hη⟩
    obtain ⟨a, b, P, hab, hcont, hcar', hsep', hlen'⟩ :=
      (LQGMetric.GM.exists_path_iff D
        (fun I l => I ⊆ A ∧ LQGMetric.Disconnects I E F ∧ l < c)).mpr ⟨η, hη⟩
    have hle : D.aroundDist A E F ≤ D.len P a b := by
      unfold ContMetric.aroundDist
      exact iInf_le_of_le a (iInf_le_of_le b
        (iInf_le_of_le P (iInf_le_of_le hab
          (iInf_le_of_le hcont (iInf_le_of_le hcar'
            (iInf_le_of_le hsep' le_rfl))))))
    exact hle.trans_lt hlen'

 

theorem aemeasurable_aroundDist_closed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (D : Ω → ContMetric) (hD : Measurable D)
    (A E F : Set ℂ) (hA : IsClosed A) :
    AEMeasurable (fun ω => (D ω).aroundDist A E F) P := by
  have hm : @Measurable (NullMeasurableSpace Ω P) ℝ≥0∞ _ _
      (fun ω => (D ω).aroundDist A E F) := by
    apply measurable_of_Iio
    intro c
    have hpre : NullMeasurableSet
        ((fun ω => (D ω).aroundDist A E F) ⁻¹' Set.Iio c) P :=
      (um_aroundDist_lt_closed A E F hA c).nullMeasurableSet_preimage
        hD.aemeasurable
    exact hpre
  exact (show NullMeasurable (fun ω => (D ω).aroundDist A E F) P from hm).aemeasurable

 

def finiteAroundCoords (D : ContMetric) : RatAnnulus → ℝ≥0∞ :=
  fun A => D.aroundDist A.toSet A.inner.toSet A.outer.toSet

theorem aemeasurable_finiteAroundCoords
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (D : Ω → ContMetric) (hD : Measurable D) :
    AEMeasurable (fun ω => finiteAroundCoords (D ω)) P := by
  apply AEMeasurable.of_eval
  intro A
  exact aemeasurable_aroundDist_closed D hD _ _ _ A.isClosed_toSet

end SupercriticalLQGUniqueness.B2.DG20Lim
