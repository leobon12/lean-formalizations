/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchRawModel

/-!
# A stopped model has a Brownian random-word SDE realization

This is an unconditional specialization of stopped K2. It exposes the exact
SDE to which the remaining stopping-time regularization argument must apply.
No raw stopping-time version or natural-filtration identification is assumed.

The relevant textbook facts are Brownian predictability (Revuz--Yor V (3.3),
p. 200) and predictable-time lifting through usual augmentation
(Dellacherie--Meyer IV.78). Applying those results requires an additional local
SLE own-filtration argument; the lifetime's announcing sequence alone does not
announce every stopping time strictly before it.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (TestOn)

namespace InteractingSLE.Wire.RetMatchGal

open Restart Restart.RetAux79 Restart.StoppedK2 Restart.DomainMarkov.Aux79 Restart.FCDet
open LawUnique Sec7.PocketTraversal Sec2.Assembly

/-- The full model state is continuous, including at finite terminal times. -/
theorem continuous_modelState {κ θ : ℝ} (M : StoppedTypeModel κ θ) (ω : M.space) :
    Continuous (fun t => (M.data.driver t ω,
      fun i => geomLW M.data.driver M.data.xL i t ω,
      fun j => geomRW M.data.driver M.data.xR j t ω)) :=
  (M.data.driverCont ω).prodMk
    ((continuous_pi fun i =>
      (isForcePath_geomLW M.data.driverCont M.data.xL ω i).1).prodMk
      (continuous_pi fun j =>
        (isForcePath_geomRW M.data.driverCont M.data.xR ω j).1))

/-- The stopped K2 construction realizes a model by a random-word SDE after
adding independent Brownian coordinates. This uses no raw-version input. -/
theorem exists_model_randomWordEvolution {κ θ : ℝ} (M : StoppedTypeModel κ θ) (hκ : 0 < κ) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (B : ℝ≥0 → M.space × (ℕ → ℝ) → ℝ),
      IsRandomWordEvolutionUpTo κ (M.law.prod P₀) ((M.data.filt 0).comap Prod.fst) univ
        (fun p => M.data.xL p.1) (fun p => M.data.xR p.1) M.data.rhoL M.data.rhoR
        (WholeField.prodFiltration (usualAugmentation M.data.filt M.law) 𝓦)
        (fun t p => M.data.driver t p.1)
        (fun i t p => geomLW M.data.driver M.data.xL i t p.1)
        (fun j t p => geomRW M.data.driver M.data.xR j t p.1) B
        (fun p => M.data.life p.1) := by
  let _ := M.probability
  let D := M.data
  have hWa := MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop D.driverAdapted
  have hLa : ∀ i, AdaptedBefore D.filt D.life (geomLW D.driver D.xL i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop
      (stronglyAdapted_geomLW D.driverAdapted D.driverCont D.xLMeas i)
  have hRa : ∀ j, AdaptedBefore D.filt D.life (geomRW D.driver D.xR j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop
      (stronglyAdapted_geomRW D.driverAdapted D.driverCont D.xRMeas j)
  have hcf := isCouplingCharFun_of_hasSafeLaw D.shiftedField
    (fun ψ : TestOn upperHalfPlaneOpens =>
      (LQGMetric.measurable_distOn_apply ψ).comp D.shiftedMeas) D.safeLaw
    (ae_of_all _ (isForceReg_thr D.driverZero D.driverCont D.xL D.xR D.life))
    (ae_of_all _ fun ω h => absurd (mem_univ ω) h) hWa hLa hRa
  have hWaU : StronglyAdapted (usualAugmentation D.filt M.law) D.driver := fun t =>
    (D.driverAdapted t).mono (Ito.le_usualAugmentation D.filt M.law t)
  have hVU : IsStoppingTime (usualAugmentation D.filt M.law)
      fun ω => (D.life ω : WithTop ℝ≥0) := fun t =>
    Ito.le_usualAugmentation D.filt M.law t _ (D.lifeStop t)
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ :=
    isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
      (𝒢 := D.filt 0) hκ (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
      (Ito.le_usualAugmentation D.filt M.law 0) MeasurableSet.univ D.xLMeas D.xRMeas
      D.xLNonpos D.xRNonneg D.xLAnti D.xRMono D.driverZero D.driverCont hWaU
      hVU D.announcing D.integrable hcf (D.lifeThreshold.mono fun _ h _ => h)
  refine ⟨P₀, hP₀, 𝓦, B, ?_⟩
  simpa only [preimage_univ] using hE

end InteractingSLE.Wire.RetMatchGal
