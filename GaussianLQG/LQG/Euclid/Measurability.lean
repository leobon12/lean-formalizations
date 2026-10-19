import GaussianLQG.Core.InterfacesEuclid
import GaussianLQG.LQG.Scaling

/-!
# Measurability of the Euclidean error (blueprint Lemma `lem:euclidean`, Step 4)

`𝖤_γ(R) = sup_{z,w ∈ B̄_R(0)} |e^{-b_γ} D^γ(z,w) - |z - w||` is a random variable
(`Setup.measurable_euclidErr`): the function `(z, w) ↦ |e^{-b} D(z,w) - |z - w||` is continuous, so
the supremum may be taken over a countable dense subset of `B̄_R(0) × B̄_R(0)`
(`measurable_biSup_of_continuousOn`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG

namespace Setup

variable (S : Setup)

/-- `𝖤_γ(R)` as a supremum over pairs. -/
theorem euclidErr_eq_biSup_pairs (γ R : ℝ) (ω : Coord) :
    S.euclidErr γ R ω = ⨆ p ∈ Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R,
      ENNReal.ofReal |Real.exp (-S.b γ) * (S.D γ ω).1 p - ‖p.1 - p.2‖| := by
  unfold euclidErr
  refine le_antisymm (iSup₂_le fun z hz => iSup₂_le fun w hw => ?_) (iSup₂_le fun p hp => ?_)
  · exact le_iSup₂ (f := fun (p : ℂ × ℂ)
      (_ : p ∈ Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R) =>
        ENNReal.ofReal |Real.exp (-S.b γ) * (S.D γ ω).1 p - ‖p.1 - p.2‖|) (z, w) ⟨hz, hw⟩
  · exact le_iSup₂_of_le p.1 hp.1 (le_iSup₂_of_le p.2 hp.2 le_rfl)

/-- **Blueprint Lemma `lem:euclidean`, measurability.** `𝖤_γ(R)` is a random variable. -/
theorem measurable_euclidErr (γ R : ℝ) : Measurable (S.euclidErr γ R) := by
  have h : S.euclidErr γ R = fun ω =>
      ⨆ p ∈ Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R,
        ENNReal.ofReal |Real.exp (-S.b γ) * (S.D γ ω).1 p - ‖p.1 - p.2‖| :=
    funext (S.euclidErr_eq_biSup_pairs γ R)
  rw [h]
  refine measurable_biSup_of_continuousOn _ (fun ω => ?_) (fun p => ?_)
  · refine Continuous.continuousOn ?_
    have hD : Continuous fun p : ℂ × ℂ => (S.D γ ω).1 p := (S.D γ ω).1.continuous
    exact ENNReal.continuous_ofReal.comp
      (continuous_abs.comp ((continuous_const.mul hD).sub (by fun_prop)))
  · exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (((S.measurable_D_apply γ p).const_mul _).sub_const _))

end Setup

end GaussianLQG
