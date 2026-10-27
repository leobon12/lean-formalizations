import MatedCRTHarmonic.GMS4.Prop410Rooting
import MatedCRTHarmonic.GMSLemma27.CellModel
import Mathlib.Probability.Independence.Basic
import MatedCRTHarmonic.GMSAppA.LemmaA1A2
import MatedCRTHarmonic.GMS4.Prop210
import MatedCRTHarmonic.GMS4.CellGraphInterface
import MatedCRTHarmonic.GMS4.Prop48
import MatedCRTHarmonic.GMS4.SmallRootMass
import MatedCRTHarmonic.GMSLemma27.Consumers

/-!
# Real and lower integrals for Proposition 2.10

Proposition 4.10 uses finite real integrals. Proposition 2.10's graph event
uses lower Lebesgue integrals. The conversion is valid for nonnegative,
integrable products; these conditions are needed when applying (4.20).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4F

/-- An admissible Proposition 2.10 test is integrable on its bounded domain.
The test need not be measurable outside that domain. -/
theorem prop210_admissible_test_integrableOn
    {ε rho C beta : ℝ} {D : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop210Admissible ε rho C beta D f) : IntegrableOn f D := by
  rcases hadm with ⟨hε0, _hε1, _hρ0, _hρ1, hC, _hβ,
    hopen, _hconn, hsubset, _hboundary, hbounds, hlipTest⟩
  have hD : MeasurableSet D := hopen.measurableSet
  have hK : 0 ≤ C * ε ^ (-beta) :=
    mul_nonneg (by linarith : 0 ≤ C) (Real.rpow_nonneg hε0.le _)
  let K : NNReal := ⟨C * ε ^ (-beta), hK⟩
  have hlips : LipschitzOnWith K f D :=
    LipschitzOnWith.of_dist_le_mul (fun z hz w hw => by
      change |f z - f w| ≤ (C * ε ^ (-beta)) * dist z w
      exact hlipTest z hz w hw)
  have hcont : ContinuousOn f D := hlips.continuousOn
  have hfin : volume D < ⊤ :=
    (measure_mono hsubset).trans_lt measure_ball_lt_top
  refine ⟨hcont.aestronglyMeasurable hD,
    HasFiniteIntegral.restrict_of_bounded (C * ε ^ (-beta)) hfin ?_⟩
  exact (ae_restrict_iff' hD).2
    (Filter.Eventually.of_forall fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbounds z hz).1]
      exact (hbounds z hz).2)

theorem setLIntegral_ofReal_mul_eq_of_integrable
    (D : Set ℂ) (f g : ℂ → ℝ)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (hInt : IntegrableOn (fun z => f z * g z) D) :
    (∫⁻ z in D, ENNReal.ofReal (f z) * ENNReal.ofReal (g z)) =
      ENNReal.ofReal (∫ z in D, f z * g z) := by
  rw [ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun z => mul_nonneg (hf z) (hg z))]
  congr 1
  funext z
  exact (ENNReal.ofReal_mul (hf z)).symm

/-- The form needed for a Proposition 2.10 test: nonnegativity is required
only on its integration domain. -/
theorem setLIntegral_ofReal_mul_eq_of_integrableOn
    (D : Set ℂ) (hD : MeasurableSet D) (f g : ℂ → ℝ)
    (hf : ∀ z ∈ D, 0 ≤ f z) (hg : ∀ z ∈ D, 0 ≤ g z)
    (hInt : IntegrableOn (fun z => f z * g z) D) :
    (∫⁻ z in D, ENNReal.ofReal (f z) * ENNReal.ofReal (g z)) =
      ENNReal.ofReal (∫ z in D, f z * g z) := by
  have hnn : ∀ᵐ z ∂volume.restrict D, 0 ≤ f z * g z :=
    (ae_restrict_iff' hD).2
      (Filter.Eventually.of_forall fun z hz => mul_nonneg (hf z hz) (hg z hz))
  rw [ofReal_integral_eq_lintegral_ofReal hInt hnn]
  apply lintegral_congr_ae
  exact (ae_restrict_iff' hD).2
    (Filter.Eventually.of_forall fun z hz => (ENNReal.ofReal_mul (hf z hz)).symm)

/-- A finite real integral bound transfers to the lower-integral inequality
used by Proposition 2.10. -/
theorem lintegral_bound_of_real_integral_bound
    (D : Set ℂ) (hD : MeasurableSet D) (f g : ℂ → ℝ)
    (hf : ∀ z ∈ D, 0 ≤ f z) (hg : ∀ z ∈ D, 0 ≤ g z)
    (hInt : IntegrableOn (fun z => f z * g z) D)
    (hIntf : IntegrableOn f D)
    {A threshold eta : ℝ} (hA : 0 ≤ A)
    (hthreshold : 0 ≤ threshold) (heta : threshold ≤ eta)
    (hbound : (∫ z in D, f z * g z) ≤
      A * (∫ z in D, f z) + threshold) :
    (∫⁻ z in D, ENNReal.ofReal (f z) * ENNReal.ofReal (g z)) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) +
        ENNReal.ofReal eta := by
  have hfnn : ∀ᵐ z ∂volume.restrict D, 0 ≤ f z :=
    (ae_restrict_iff' hD).2 (Filter.Eventually.of_forall hf)
  have hIf : 0 ≤ ∫ z in D, f z := integral_nonneg_of_ae hfnn
  have hEta0 : 0 ≤ eta := hthreshold.trans heta
  have hIfEq : (∫⁻ z in D, ENNReal.ofReal (f z)) =
      ENNReal.ofReal (∫ z in D, f z) :=
    (ofReal_integral_eq_lintegral_ofReal hIntf hfnn).symm
  rw [setLIntegral_ofReal_mul_eq_of_integrableOn D hD f g hf hg hInt, hIfEq]
  calc
    ENNReal.ofReal (∫ z in D, f z * g z) ≤
        ENNReal.ofReal (A * (∫ z in D, f z) + threshold) :=
      ENNReal.ofReal_le_ofReal hbound
    _ ≤ ENNReal.ofReal (A * (∫ z in D, f z) + eta) :=
      ENNReal.ofReal_le_ofReal (add_le_add_right heta _)
    _ = ENNReal.ofReal A * ENNReal.ofReal (∫ z in D, f z) +
          ENNReal.ofReal eta := by
      rw [ENNReal.ofReal_add (mul_nonneg hA hIf) hEta0, ENNReal.ofReal_mul hA]

end MatedCRTHarmonic.GMS4F

