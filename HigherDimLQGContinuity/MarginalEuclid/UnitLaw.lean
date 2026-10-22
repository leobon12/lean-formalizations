import HigherDimLQGContinuity.Rotation.Law
import HigherDimLQGContinuity.Norm.Scaling
import HigherDimLFPP.Lower.Frames

/-!
# The law of the normalized distance in every unit direction

Rotation invariance of a strong metric gives the same one-point law at every
unit vector. The deterministic mean-log normalization preserves that law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- The unit-direction law of the mean-log normalized strong metric. -/
theorem law_rho_unit {d : ℕ} (hd : 3 ≤ d) (hR : StrongRotLaw d)
    {ξ : ℝ} (hξ : 0 < ξ) (hgap : Real.sqrt (2 * d) < distExp d ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {u : Rd d} (hu : ‖u‖ = 1) :
    (normLGFLaw d).map (fun g => (rho D g).1 (0, u)) =
      (normLGFLaw d).map (fun g => (rho D g).1 (0, e₁ d)) := by
  let O := HigherDimLFPP.Lower.edgeRot u
  let O₂ : C(Rd d × Rd d, Rd d × Rd d) :=
    ⟨fun p => (O p.1, O p.2),
      (O.continuous.comp continuous_fst).prodMk (O.continuous.comp continuous_snd)⟩
  let ev : C(Rd d × Rd d, ℝ) → ℝ := fun f => f (0, e₁ d)
  have hev : Measurable ev := (continuous_eval_const (0, e₁ d)).measurable
  have hDmap : Measurable (fun g : DistRd d => (D g).1) :=
    measurable_subtype_coe.comp hD.measurable
  have hrot := hR ξ hξ hgap D hD O
  have hraw : (normLGFLaw d).map (fun g => (D g).1 (0, u)) =
      (normLGFLaw d).map (fun g => (D g).1 (0, e₁ d)) := by
    have hleft : (fun g : DistRd d => (D g).1 (0, u)) =
        ev ∘ (fun g => (D g).1.comp O₂) := by
      funext g
      simp only [Function.comp_apply, ev, ContinuousMap.comp_apply]
      change (D g).1 (0, u) = (D g).1 (O 0, O (e₁ d))
      rw [map_zero, HigherDimLFPP.Lower.edgeRot_e₁ (by omega : 0 < d) hu]
    have hright : (fun g : DistRd d => (D g).1 (0, e₁ d)) =
        ev ∘ (fun g => (D g).1) := rfl
    rw [hleft, hright, ← Measure.map_map hev
      (by
        apply ContinuousMap.measurable_iff_eval.mpr
        intro p
        exact p2_measurable_contMetric_apply hD.measurable (O₂ p)),
      ← Measure.map_map hev hDmap, hrot]
  let sc : ℝ → ℝ := fun a => Real.exp (-logMean D) * a
  have hsc : Measurable sc := measurable_const.mul measurable_id
  have hnorm : (fun g : DistRd d => (rho D g).1 (0, u)) =
      sc ∘ (fun g => (D g).1 (0, u)) := by
    funext g
    exact rho_apply D g (0, u)
  have hnorm' : (fun g : DistRd d => (rho D g).1 (0, e₁ d)) =
      sc ∘ (fun g => (D g).1 (0, e₁ d)) := by
    funext g
    exact rho_apply D g (0, e₁ d)
  rw [hnorm, hnorm', ← Measure.map_map hsc (p2_measurable_contMetric_apply hD.measurable (0, u)),
    ← Measure.map_map hsc (p2_measurable_contMetric_apply hD.measurable (0, e₁ d)), hraw]

end HigherDimLQGContinuity
