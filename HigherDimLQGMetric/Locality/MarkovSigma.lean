import HigherDimLQGMetric.B3.Interfaces
import LQGMetric.Papers.DFGPS.L2_19

/-! The Markov reconstruction gives the full field sigma algebra from its
interior restriction and the exterior residual, up to null sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_fullSigma_le_markovSigma {d : ℕ} {Ω : Type}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (g : Ω → DistRd d) (V : TopologicalSpace.Opens (Rd d))
    (R : Ω → DistOn (extOpen V))
    (hdet : LQGMetric.AEDeterminedBy g
      (fun ω => (restrictTo V (g ω), R ω)) P)
    (M : MeasurableSpace Ω)
    (hR : MeasurableSpace.comap R inferInstance ≤ M) :
    fullSigmaRd g ≤ aeClosure P (fieldSigmaRd g V ⊔ M) := by
  obtain ⟨F, hF, hFg⟩ := hdet
  let N : MeasurableSpace Ω := fieldSigmaRd g V ⊔ M
  letI : MeasurableSpace Ω := mΩ
  have hp : Measurable[N] (fun ω => (restrictTo V (g ω), R ω)) := by
    letI : MeasurableSpace Ω := N
    have h₁ : Measurable (fun ω => restrictTo V (g ω)) :=
      (comap_measurable _).mono le_sup_left le_rfl
    have h₂ : Measurable R :=
      (comap_measurable _).mono (hR.trans le_sup_right) le_rfl
    exact h₁.prodMk h₂
  have hFg' : g =ᵐ[P] fun ω => F (restrictTo V (g ω), R ω) := by
    simpa only [Function.comp_def] using hFg
  exact LQGMetric.DFGPS.L219.comap_le_aeClosure_of_ae_eq
    (hF.comp hp) hFg'

end HigherDimLQGMetric
