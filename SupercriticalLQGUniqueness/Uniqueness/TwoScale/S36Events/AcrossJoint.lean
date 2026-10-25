import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.SphereInf




set_option autoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events

local instance : TopologicalSpace EuclideanAnnulus :=
  inferInstanceAs (TopologicalSpace
    {t : ℂ × (ℝ × ℝ) // 0 < t.2.1 ∧ t.2.1 < t.2.2})

local instance : SecondCountableTopology EuclideanAnnulus :=
  inferInstanceAs (SecondCountableTopology
    {t : ℂ × (ℝ × ℝ) // 0 < t.2.1 ∧ t.2.1 < t.2.2})

local instance : MeasurableSpace EuclideanAnnulus := borel _

local instance : OpensMeasurableSpace EuclideanAnnulus := ⟨le_rfl⟩

 

theorem acrossDist_joint_lsc :
    LowerSemicontinuous (fun p : LSCMetric × EuclideanAnnulus =>
      acrossDist p.1 p.2) := by
  have hg : Continuous (fun p : LSCMetric × EuclideanAnnulus =>
      (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  convert spherePairInf_joint_lsc.comp hg using 1
  funext p
  exact (spherePairInf_eq_acrossDist p.1 p.2).symm

 
theorem acrossDist_joint_borel :
    @Measurable (LSCMetric × EuclideanAnnulus) ENNReal (borel _) inferInstance
      (fun p => acrossDist p.1 p.2) := by
  letI : MeasurableSpace (LSCMetric × EuclideanAnnulus) := borel _
  letI : OpensMeasurableSpace (LSCMetric × EuclideanAnnulus) := ⟨le_rfl⟩
  exact acrossDist_joint_lsc.measurable

 

theorem acrossDist_joint_measurable :
    Measurable (fun p : LSCMetric × EuclideanAnnulus =>
      acrossDist p.1 p.2) :=
  acrossDist_joint_lsc.measurable

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
