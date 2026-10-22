import HigherDimLQGMetric.Local.CopiesSigma
import HigherDimLQGMetric.Select.Internal

/-!
# Borel representatives of scaled internal-metric families

On the almost-sure length-metric event, internal distances on open sets equal the
countable Borel chain formula. This supplies exact measurable observations for the
conditional-independence algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric.GM.Bilip
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

def l7b_scale (ξ : ℝ) (h : Ω → DistRd d) (r : ℝ) (z : Rd d) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z))

def l7b_intFam (ξ : ℝ) (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (r : ℝ) (z : Rd d) : Ω → Set (Rd d) → Rd d → Rd d → ℝ≥0∞ :=
  fun ω V u v => l7b_scale ξ h r z ω * (D ω).internal V u v

def l7b_chainFam (ξ : ℝ) (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (r : ℝ) (z : Rd d) : Ω → Set (Rd d) → Rd d → Rd d → ℝ≥0∞ :=
  fun ω V u v => l7b_scale ξ h r z ω * (D ω).chainInf V u v

omit [MeasurableSpace Ω] in
theorem l7b_measurable_scale {M : MeasurableSpace Ω} (ξ : ℝ)
    {h : Ω → DistRd d} (hh : Measurable[M] h) (r : ℝ) (z : Rd d) :
    Measurable[M] (l7b_scale ξ h r z) := by
  unfold l7b_scale
  exact ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.mul
      ((measurable_sphereAvg_left r z).comp hh)))

omit [MeasurableSpace Ω] in
theorem l7b_measurable_chainFam {M : MeasurableSpace Ω} (ξ : ℝ)
    {h : Ω → DistRd d} {D : Ω → ContMetric d}
    (hh : Measurable[M] h) (hD : Measurable[M] D) (r : ℝ) (z : Rd d)
    (V : Set (Rd d)) : Measurable[M] (fun ω => l7b_chainFam ξ h D r z ω V) := by
  apply measurable_pi_iff.mpr
  intro u
  apply measurable_pi_iff.mpr
  intro v
  exact (l7b_measurable_scale ξ hh r z).mul
    ((ContMetric.measurable_chainInf V).comp
      (hD.prodMk (measurable_const.prodMk measurable_const)))

/-- The scaled internal family is a.s. equal to a Borel family on every open set. -/
theorem l7b_intFam_ae_eq_chain {ξ : ℝ} {h : Ω → DistRd d} {D : Ω → ContMetric d}
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (r : ℝ) (z : Rd d)
    {V : Set (Rd d)} (hV : IsOpen V) :
    (fun ω => l7b_intFam ξ h D r z ω V) =ᵐ[P]
      (fun ω => l7b_chainFam ξ h D r z ω V) := by
  filter_upwards [hlen] with ω hω
  funext u v
  dsimp [l7b_intFam, l7b_chainFam]
  rw [(D ω).internal_eq_chainInf hω hV u v]

/-- Replace the internal-metric sigma algebra by its Borel chain representative,
up to null events. -/
theorem l7b_intSigma_le_ae_chain {ξ : ℝ} {h : Ω → DistRd d} {D : Ω → ContMetric d}
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (r : ℝ) (z : Rd d)
    {V : Set (Rd d)} (hV : IsOpen V) :
    famSigmaRd (l7b_intFam ξ h D r z) V ≤
      aeClosure P (famSigmaRd (l7b_chainFam ξ h D r z) V) := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨(fun ω => l7b_chainFam ξ h D r z ω V) ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
  filter_upwards [l7b_intFam_ae_eq_chain hlen r z hV] with ω hω
  change (l7b_intFam ξ h D r z ω V ∈ S) = (l7b_chainFam ξ h D r z ω V ∈ S)
  rw [hω]

/-- The Borel chain representative is likewise measurable from the actual internal family
up to null events. -/
theorem l7b_chainSigma_le_ae_int {ξ : ℝ} {h : Ω → DistRd d} {D : Ω → ContMetric d}
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) (r : ℝ) (z : Rd d)
    {V : Set (Rd d)} (hV : IsOpen V) :
    famSigmaRd (l7b_chainFam ξ h D r z) V ≤
      aeClosure P (famSigmaRd (l7b_intFam ξ h D r z) V) := by
  rintro s ⟨S, hS, rfl⟩
  refine ⟨(fun ω => l7b_intFam ξ h D r z ω V) ⁻¹' S, ⟨S, hS, rfl⟩, ?_⟩
  filter_upwards [l7b_intFam_ae_eq_chain hlen r z hV] with ω hω
  change (l7b_chainFam ξ h D r z ω V ∈ S) = (l7b_intFam ξ h D r z ω V ∈ S)
  rw [hω]

end HigherDimLQGMetric
