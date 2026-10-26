import SupercriticalConformalCovariance.Small.CommonFixed
import SupercriticalConformalCovariance.Transport.LawTransfer

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace

namespace SupercriticalConformalCovariance.Small
open LQGMetric (DistC IsWholePlaneGFF ofCont)
open SupercriticalConformalCovariance (IsDomainRealization)

universe u v w

/-- The shared field retains the whole-plane GFF law. -/
theorem commonFixedMeasure_wholePlaneGFF
    {Y : Type v} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → DistC) (R : ℕ → Ω → Y) (μ : Measure DistC)
    [IsProbabilityMeasure μ] (y0 : Y)
    (hG : IsWholePlaneGFF (H 0) P) (hμ : P.map (H 0) = μ) :
    IsWholePlaneGFF (fun path : ℕ → DistC × Y => (path 0).1)
      (commonFixedMeasure P H R μ y0) := by
  apply LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq (by fun_prop) hG
  rw [commonFixedMeasure_field P H R μ y0, hμ]

/-- Transfer a local realization through the common-field trajectory coupling. -/
theorem commonFixedMeasure_realization
    {F : Type u} {Y : Type v} [MeasurableSpace F] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) (μ : Measure F)
    [IsProbabilityMeasure μ] (y0 : Y) (n : ℕ)
    (hH : Measurable (H n)) (hR : Measurable (R n))
    (hμ : P.map (H n) = μ) (V : Opens ℂ)
    (J : F × Y → SupercriticalConformalCovariance.Transport.RealizationData V) (hJ : Measurable J)
    (hreal : IsDomainRealization V P
      (fun ω => (J (H n ω, R n ω)).1)
      (fun ω => (J (H n ω, R n ω)).2.1)
      (fun ω => (J (H n ω, R n ω)).2.2.1))
    (hwp : IsWholePlaneGFF
      (fun ω => (J (H n ω, R n ω)).2.1 -
        ofCont (J (H n ω, R n ω)).2.2.2) P) :
    IsDomainRealization V (commonFixedMeasure P H R μ y0)
      (fun path => (J ((path 0).1, (path (n+1)).2)).1)
      (fun path => (J ((path 0).1, (path (n+1)).2)).2.1)
      (fun path => (J ((path 0).1, (path (n+1)).2)).2.2.1) := by
  let M := commonFixedMeasure P H R μ y0
  have hM : IsProbabilityMeasure M := by dsimp [M, commonFixedMeasure]; infer_instance
  let pairOld : Ω → F × Y := fun ω => (H n ω, R n ω)
  let pairNew : (ℕ → F × Y) → F × Y :=
    fun path => ((path 0).1, (path (n+1)).2)
  have hpOld : Measurable pairOld := hH.prodMk hR
  have hpNew : Measurable pairNew := by fun_prop
  have hpair : M.map pairNew = P.map pairOld :=
    commonFixedMeasure_pair P H R μ y0 n hH hR hμ
  have hlaw : M.map (J ∘ pairNew) = P.map (J ∘ pairOld) := by
    rw [← Measure.map_map hJ hpNew, hpair, Measure.map_map hJ hpOld]
  exact SupercriticalConformalCovariance.Transport.realization_of_joint_law_eq V P M (J ∘ pairOld)
    (J ∘ pairNew) (hJ.comp hpOld) (hJ.comp hpNew) hreal hwp hlaw

end SupercriticalConformalCovariance.Small
