import SupercriticalLQGUniqueness.B2.PfeAxioms.NonDiracGFF

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem aemeasurable_of_map_eq_nondirac
    {Ω Ω' A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (f : Ω' → A) (g : Ω → A)
    (hg : AEMeasurable g P)
    (hnon : ∀ a : A, P.map g ≠ Measure.dirac a)
    (hlaw : P'.map f = P.map g) :
    AEMeasurable f P' := by
  by_contra hf
  have hdir := Measure.map_of_not_aemeasurable_of_ne_zero hf
    (by
      intro h0
      have h1 := congrArg (fun μ : Measure Ω' => μ Set.univ) h0
      simp at h1)
  exact hnon _ (hlaw.symm.trans hdir)

 

theorem gff_joint_law_ne_dirac
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P)
    (G : Ω → A)
    (hG : AEMeasurable G P) (a : DistC × A) :
    P.map (fun ω => (h ω, G ω)) ≠ Measure.dirac a := by
  intro hdir
  have hp : AEMeasurable (fun ω => (h ω, G ω)) P :=
    hh.measurable.aemeasurable.prodMk hG
  have hfst : (P.map (fun ω => (h ω, G ω))).map Prod.fst = P.map h := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hp]
    rfl
  have hdir' : P.map h = Measure.dirac a.1 := by
    rw [← hfst, hdir]
    rw [Measure.map_dirac' measurable_fst]
  exact wholePlaneGFF_map_ne_dirac P h hh a.1 hdir'

end SupercriticalLQGUniqueness.B2.PfeAxioms
