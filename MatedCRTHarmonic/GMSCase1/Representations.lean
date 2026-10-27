import MatedCRTHarmonic.GMSCase1.Case2Local
import MatedCRTHarmonic.GMS4.Prop210
import MatedCRTHarmonic.GMS4.CellGraphInterface
import MatedCRTHarmonic.GMS4.Prop48
import MatedCRTHarmonic.GMS4.Prop410Rooting
import MatedCRTHarmonic.GMS4.SmallRootMass
import MatedCRTHarmonic.GMSLemma27.Consumers
import MatedCRTHarmonic.ConeLemmaA10.ProductRooting
import MatedCRTHarmonic.CellScaling.JointScalingOClock

/-!
# Source representations of the Case 1/2 fields and the area-time curve

Source: [18, Proposition 4.10, Cases 1–2].

* `ae_rootedWPField_eq`: on the marked carrier, almost surely
  `h₁ = h₀ − γ log|·−z| + γ log max(|·|,1)` exactly as printed (the unit-circle renormalization in
  CANON's `rootedField` is a.s. trivial for `z ∈ 𝔻`; the rooting construction's `ProductRooting`).
* `ae_case2Field_eq`: almost surely `h₂ = h₀ − γ log|·−z|` ([18]), the representation used
  by the Case 3/4 laws (`GMSCase/*`).
* `rootedWPData_areaCurve_law`: the Case 1 joint law extended by the area-parametrized curve of
  the field, the area-scaling construction's measurable `JointScalingO.parMap γ (h, ηL)` (`= ηL` reparametrized by `μ_h`
  whenever such a parametrization exists, `JointScalingO.parEval_eq`): the whole-plane cell model
  `ηWP` is carried along by the rooting.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.MatedCRT

/-- DMS's rooting shift minus `γ log max(|·|, 1)` is the source's `−γ log|· − z|`. -/
theorem logRootingShift_sub_logMax (γ : ℝ) (z : ℂ) :
    ConeLemmaA10.logRootingShift γ z - CellScaling.ofFunC (fun w => γ * Real.log (max ‖w‖ 1)) =
      CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z‖) := by
  have h₁ : LocallyIntegrableOn (fun w : ℂ => -γ * Real.log ‖w - z‖)
      ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) volume := by
    have h := ((ConeLemmaA10.locallyIntegrable_log_norm_sub z).smul (-γ)).congr
      (ae_of_all _ fun w => by simp : ∀ᵐ w ∂volume,
        ((-γ) • fun w : ℂ => Real.log ‖w - z‖) w = -γ * Real.log ‖w - z‖)
    simpa [locallyIntegrableOn_univ] using h
  have h₂ : LocallyIntegrableOn (fun w : ℂ => γ * Real.log (max ‖w‖ 1))
      ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) volume := by
    have h := (ConeLemmaA10.continuous_log_max_norm_one.locallyIntegrable (μ := volume)).smul γ
    have h' : LocallyIntegrable (fun w : ℂ => γ * Real.log (max ‖w‖ 1)) volume :=
      h.congr (ae_of_all _ fun w => by simp)
    simpa [locallyIntegrableOn_univ] using h'
  have e : ConeLemmaA10.logRootingShift γ z =
      CellScaling.ofFunC (fun w => -γ * Real.log ‖w - z‖) +
        CellScaling.ofFunC (fun w => γ * Real.log (max ‖w‖ 1)) := by
    rw [ConeLemmaA10.logRootingShift, CellScaling.ofFunC, CellScaling.ofFunC,
      ← Distribution.ofFun_add h₁ h₂]
    rfl
  rw [e, add_sub_cancel_right]

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

theorem ae_rootMeasure_mem_ball : ∀ᵐ z ∂Canon.rootMeasure, z ∈ ball (0 : ℂ) 1 := by
  change ∀ᵐ z ∂(ENNReal.ofReal (Real.pi⁻¹) •
    (volume.restrict GMS4.GMSA.rootingDisk)), z ∈ ball (0 : ℂ) 1
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_ball) _

/-- **The Case 1 field as printed.** Almost surely on the marked carrier,
`h₁ = h₀ + (−γ log|·−z| + γ log max(|·|,1))`. -/
theorem ae_rootedWPField_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ v ∂Canon.rootedLaw P,
      rootedWPField γ X₀ v = wpField X₀ v.1 + ConeLemmaA10.logRootingShift γ v.2 := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact ConeLemmaA10.ae_normalizedRootingMap_eq_add_logRootingShift_prod
    (isNormalizedWPGFF_wpField D) γ ae_rootMeasure_mem_ball

/-- **The Case 2 field as printed** ([18] ): almost surely `h₂ = h₀ − γ log|·−z|`. -/
theorem ae_case2Field_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ v ∂Canon.rootedLaw P,
      Canon.case2Field γ (wpField X₀ v.1) v.2 =
        wpField X₀ v.1 + CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖) := by
  filter_upwards [ae_rootedWPField_eq D] with v hv
  change rootedWPField γ X₀ v - _ = _
  rw [hv, add_sub_assoc, logRootingShift_sub_logMax]

/-! ## The area-time curve -/

/-- The whole-plane data together with the area-parametrized curve `t ↦ ηL(τ_h(t))` of its field
(the area-scaling construction's measurable `JointScalingO.parMap`). -/
def withAreaCurve (γ : ℝ) (x : WPData) : WPData × (DistC × (ℝ → ℂ)) :=
  (x, CellScaling.JointScalingO.parMap γ (x.1, x.2.2))

theorem measurable_withAreaCurve (γ : ℝ) : Measurable (withAreaCurve γ) :=
  measurable_id.prodMk ((CellScaling.JointScalingO.measurable_parMap γ).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

/-- **Case 1 with the whole-plane cell model.** The joint law of the rooted data and the
area-parametrized curve of the rooted field is the `μ_{h₀}(𝔻)/π`-weighted law of the unrooted
data and the area-parametrized curve of `h₀`. -/
theorem rootedWPData_areaCurve_law
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    (Canon.rootedLaw P).map (fun v => withAreaCurve γ (rootedWPData γ X₀ hIG₀ U ηL v)) =
      (P.withDensity fun ω =>
        (Canon.referenceSample D hγ ω).wholePlaneArea (ball 0 1) /
          ENNReal.ofReal Real.pi).map (fun ω => withAreaCurve γ (wpData X₀ hIG₀ U ηL ω)) := by
  have hac : AEMeasurable (wpData X₀ hIG₀ U ηL) (P.withDensity fun ω =>
      (Canon.referenceSample D hγ ω).wholePlaneArea (ball 0 1) / ENNReal.ofReal Real.pi) :=
    (aemeasurable_wpData D hγ).mono_ac (withDensity_absolutelyContinuous _ _)
  have e1 := AEMeasurable.map_map_of_aemeasurable (measurable_withAreaCurve γ).aemeasurable
    (aemeasurable_rootedWPData D hγ)
  have e2 := AEMeasurable.map_map_of_aemeasurable (measurable_withAreaCurve γ).aemeasurable hac
  rw [← Function.comp_def, ← e1, rootedWPData_law D hγ, e2]
  rfl

end Coupling

end MatedCRTHarmonic.GMSCase1
