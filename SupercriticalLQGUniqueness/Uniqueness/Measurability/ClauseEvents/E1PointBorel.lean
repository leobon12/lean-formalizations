import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.InternalGeoCode
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.LoopCover
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.AcrossJoint




 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

local instance : TopologicalSpace EuclideanAnnulus :=
  inferInstanceAs (TopologicalSpace
    {t : ℂ × (ℝ × ℝ) // 0 < t.2.1 ∧ t.2.1 < t.2.2})

local instance : SecondCountableTopology EuclideanAnnulus :=
  inferInstanceAs (SecondCountableTopology
    {t : ℂ × (ℝ × ℝ) // 0 < t.2.1 ∧ t.2.1 < t.2.2})

local instance : MeasurableSpace EuclideanAnnulus := borel _

local instance : BorelSpace EuclideanAnnulus := ⟨rfl⟩

local instance : OpensMeasurableSpace EuclideanAnnulus := ⟨le_rfl⟩

abbrev E1Delta (q : Ioo (0 : ℝ) (1 / 100)) := Ioc (0 : ℝ) (q : ℝ)

private theorem delta_lt_one (q : Ioo (0 : ℝ) (1 / 100))
    (δ : E1Delta q) : (δ : ℝ) < 1 := by
  have hq := q.2.2
  have hδ := δ.2.2
  linarith

def e1Annulus (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (p : ℂ × E1Delta q) :
    EuclideanAnnulus :=
  ⟨(p.1, ((p.2 : ℝ) * r, Real.sqrt (p.2 : ℝ) * r)),
    TwoScale.Consolidated.loop_annulus_valid r.2 p.2.2.1 (delta_lt_one q p.2)⟩

private theorem e1Annulus_continuous (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) :
    Continuous (e1Annulus r q) := by
  have hδ : Continuous (fun p : ℂ × E1Delta q => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hData : Continuous (fun p : ℂ × E1Delta q =>
      (p.1, ((p.2 : ℝ) * r, Real.sqrt (p.2 : ℝ) * r))) :=
    continuous_fst.prodMk ((hδ.mul continuous_const).prodMk
      ((Real.continuous_sqrt.comp hδ).mul continuous_const))
  exact Continuous.subtype_mk hData _

attribute [local irreducible] e1Annulus

private theorem e1Across_measurable (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) :
    Measurable (fun p : LSCMetric × (ℂ × E1Delta q) =>
      acrossDist p.1 (e1Annulus r q p.2)) := by
  let f : LSCMetric × EuclideanAnnulus → ENNReal :=
    fun p => acrossDist p.1 p.2
  let g : LSCMetric × (ℂ × E1Delta q) → LSCMetric × EuclideanAnnulus :=
    fun p => (p.1, e1Annulus r q p.2)
  have hAnn : Measurable (fun p : LSCMetric × (ℂ × E1Delta q) =>
      e1Annulus r q p.2) := (e1Annulus_continuous r q).measurable.comp measurable_snd
  have hg : Measurable g := measurable_fst.prodMk hAnn
  have hf : Measurable f := TwoScale.S36Events.acrossDist_joint_measurable
  have hcomp : Measurable (f ∘ g) := hf.comp hg
  exact hcomp

private theorem e1Loop_measurable (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) :
    Measurable (fun p : LSCMetric × (ℂ × E1Delta q) =>
      TwoScale.Consolidated.loopF p.1 p.2.1 r p.2.2) := by
  let g : LSCMetric × (ℂ × E1Delta q) → LSCMetric × (ℂ × (ℝ × ℝ)) :=
    fun p => (p.1, (p.2.1, ((p.2.2 : ℝ) * r, Real.sqrt (p.2.2 : ℝ) * r)))
  have hx : Measurable (fun p : LSCMetric × (ℂ × E1Delta q) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hδ : Measurable (fun p : LSCMetric × (ℂ × E1Delta q) =>
      (p.2.2 : ℝ)) := measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hg : Measurable g :=
    measurable_fst.prodMk (hx.prodMk
      ((hδ.mul measurable_const).prodMk (hδ.sqrt.mul measurable_const)))
  exact TwoScale.Consolidated.measurable_aroundRat.comp hg

private theorem e1Scale_measurable (q : Ioo (0 : ℝ) (1 / 100))
    (θ : Ioi (0 : ℝ)) :
    Measurable (fun p : LSCMetric × (ℂ × E1Delta q) =>
      ENNReal.ofReal ((p.2.2 : ℝ) ^ (θ : ℝ))) := by
  have hδ : Measurable (fun p : LSCMetric × (ℂ × E1Delta q) =>
      (p.2.2 : ℝ)) := measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  exact ENNReal.continuous_ofReal.measurable.comp (hδ.pow_const _)

attribute [local irreducible] TwoScale.Consolidated.loopF acrossDist

 
theorem e1PointBad_measurable (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (θ : Ioi (0 : ℝ)) :
    MeasurableSet {p : LSCMetric × (ℂ × E1Delta q) |
      ENNReal.ofReal ((p.2.2 : ℝ) ^ (θ : ℝ)) *
        acrossDist p.1 (e1Annulus r q p.2) <
          TwoScale.Consolidated.loopF p.1 p.2.1 r p.2.2} := by
  have hAcross := e1Across_measurable r q
  have hAround := e1Loop_measurable r q
  have hPow := e1Scale_measurable q θ
  exact measurableSet_lt (hPow.mul hAcross) hAround

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
