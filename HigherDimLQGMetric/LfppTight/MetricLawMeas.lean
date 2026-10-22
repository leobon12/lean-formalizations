import HigherDimLQGMetric.LfppTight.MeasurableMetric
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLFPP.Paths.Measurable

/-!
# Measurability of a random LFPP metric

Coordinatewise measurability of the convolution field and almost-sure continuity
give measurability of its whole-space LFPP metric as a continuous map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_aemeasurable_lfppMetricLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ξ a : ℝ) (H : Rd d → Ω → ℝ)
    (hm : ∀ z, AEMeasurable (H z) P)
    (hc : ∀ᵐ ω ∂P, Continuous fun z => H z ω) :
    AEMeasurable (fun ω => toCMapRd
      (a • fun p : Rd d × Rd d =>
        HigherDimLFPP.lfppDistOn ξ (fun z => H z ω) Set.univ p.1 p.2)) P := by
  classical
  let Y : Rd d → Ω → ℝ := fun z ω =>
    if hcont : Continuous (fun z => H z ω) then H z ω else 0
  have hYc : ∀ ω, Continuous fun z => Y z ω := by
    intro ω
    by_cases hcont : Continuous (fun z => H z ω)
    · have heq : (fun z => Y z ω) = fun z => H z ω := by
        funext z
        exact dite_eq_left hcont
      rwa [heq]
    · have heq : (fun z => Y z ω) = fun _ => 0 := by
        funext z
        exact dite_eq_right hcont
      rw [heq]
      exact continuous_const
  have hYm : ∀ z, AEMeasurable (Y z) P := by
    intro z
    have heq : Y z =ᵐ[P] H z := by
      filter_upwards [hc] with ω hω
      exact dite_eq_left hω
    exact (aemeasurable_congr heq.symm).1 (hm z)
  have hCM := l10a_aemeasurable_toContMap Y hYm hYc
  have hpoint : ∀ p : Rd d × Rd d,
      AEMeasurable (fun ω => a *
        HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) Set.univ p.1 p.2) P := by
    intro p
    have hF : Measurable (fun φ : C(Rd d, ℝ) => a *
        HigherDimLFPP.lfppDistOn ξ φ Set.univ p.1 p.2) :=
      (HigherDimLFPP.measurable_lfppDistOn_continuousMap
        (V := Set.univ) isOpen_univ ξ p.1 p.2).const_mul a
    have hA := hF.comp_aemeasurable hCM
    simpa only [Function.comp_def, ContinuousMap.coe_mk] using hA
  have hcont : ∀ ω, Continuous (fun p : Rd d × Rd d => a *
      HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) Set.univ p.1 p.2) := by
    intro ω
    have heq : (fun p : Rd d × Rd d =>
        HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) Set.univ p.1 p.2) =
        fieldLfpp ξ (fun z => Y z ω) := by
      funext p
      exact (fieldLfpp_eq_lfppDistOn (hYc ω) p).symm
    have hF : Continuous (fun p => a * fieldLfpp ξ (fun z => Y z ω) p) :=
      (continuous_fieldLfpp (hYc ω)).const_mul a
    convert hF using 1
    funext p
    exact congrFun heq p |>.symm ▸ rfl
  have hmap := l6a_aemeasurable_toCMapRd P
    (fun ω p => a * HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) Set.univ p.1 p.2)
    hpoint (Filter.Eventually.of_forall hcont)
  have heq : (fun ω => toCMapRd
      (fun p : Rd d × Rd d => a *
        HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) Set.univ p.1 p.2)) =ᵐ[P]
      (fun ω => toCMapRd (a • fun p : Rd d × Rd d =>
        HigherDimLFPP.lfppDistOn ξ (fun z => H z ω) Set.univ p.1 p.2)) := by
    filter_upwards [hc] with ω hω
    congr 1
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, Y, dite_eq_left hω]
  exact (aemeasurable_congr heq).1 hmap

end HigherDimLQGMetric
