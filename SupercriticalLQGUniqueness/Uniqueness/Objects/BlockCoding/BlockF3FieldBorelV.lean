import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockF3FieldBorel




set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
open LQGMetric (DistC)

theorem measurable_block_f3v (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (D E : DistC → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (hRad : 0 ≤ T.blockRadius) :
    Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T =>
      Objects.Shadow.circleOuter (Objects.Excursions.cV T) T.blockRadius.toNNReal 0
        (sphere (Objects.Excursions.cV T) T.blockRadius \
          Objects.Producer.goodSet (D p.1) (Objects.Excursions.cV T) p.2.1.2 T.blockRadius
            (C.lamConst * (E p.1 ((p.2.1.1 : ℂ), (p.2.1.2 : ℂ))).toReal)
            p.2.1.2.property)) := by
  let R : NNReal := ⟨T.blockRadius, hRad⟩
  have hRadEq : (R : ℝ) = T.blockRadius := rfl
  have hRto : R = T.blockRadius.toNNReal := by
    apply Subtype.ext
    exact (Real.coe_toNNReal T.blockRadius hRad).symm
  have hD' : Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T => D p.1) :=
    hD.comp measurable_fst
  have hE' : Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T => E p.1) :=
    hE.comp measurable_fst
  have hu : Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T =>
      (p.2.1.1 : ℂ)) := by fun_prop
  have hv : Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T =>
      (p.2.1.2 : ℂ)) := by fun_prop
  have hVSub : Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T =>
      (⟨(p.2.1.2 : ℂ), by simpa only [hRadEq] using p.2.1.2.property⟩ :
        closedBall (Objects.Excursions.cV T) (R : ℝ))) := by fun_prop
  have hEval : Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T =>
      E p.1 ((p.2.1.1 : ℂ), (p.2.1.2 : ℂ))) :=
    TwoScale.S36Events.jointEval_lsc.measurable.comp (hE'.prodMk (hu.prodMk hv))
  have hTh : Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T =>
      C.lamConst * (E p.1 ((p.2.1.1 : ℂ), (p.2.1.2 : ℂ))).toReal) :=
    measurable_const.mul (ENNReal.measurable_toReal.comp hEval)
  have hInput : Measurable (fun p : DistC × Objects.BlockWitness.BlockWitness T =>
      Prod.mk (D p.1) (Prod.mk
        (⟨(p.2.1.2 : ℂ), by simpa only [hRadEq] using p.2.1.2.property⟩ :
          closedBall (Objects.Excursions.cV T) (R : ℝ))
        (C.lamConst * (E p.1 ((p.2.1.1 : ℂ), (p.2.1.2 : ℂ))).toReal))) :=
    hD'.prodMk (hVSub.prodMk hTh)
  have hM := (Objects.BlockWitness.measurable_circle_bad (Objects.Excursions.cV T) R).comp hInput
  convert hM using 1
  funext p
  simp only [Function.comp_def]
  let S : Set ℂ := sphere (Objects.Excursions.cV T) T.blockRadius \
    Objects.Producer.goodSet (D p.1) (Objects.Excursions.cV T) p.2.1.2 T.blockRadius
      (C.lamConst * (E p.1 ((p.2.1.1 : ℂ), (p.2.1.2 : ℂ))).toReal)
      p.2.1.2.property
  change Objects.Shadow.circleOuter (Objects.Excursions.cV T) T.blockRadius.toNNReal 0 S =
    Objects.Shadow.circleOuter (Objects.Excursions.cV T) R 0 S
  rw [hRto]


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
