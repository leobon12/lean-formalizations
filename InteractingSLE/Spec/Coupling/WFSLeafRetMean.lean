/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafJointGaussian
import LQGMetric.Field.RandomDistVersion

/-!
# A common retained mean from countably many frozen-mean limits

The code consists of Borel approximants to the pairings with `comb c`, for
the countable family `CoordJ`. LQGMetric's measurable inverse `pairJInv`
constructs one distribution-valued reader. Whenever the limits are the
pairings of an actual local-set mean, this reader is that mean almost surely,
simultaneously at every test. No independent admissibility or finite-order
assumption on the code is needed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology

namespace InteractingSLE.WFS

open LQGMetric LocalSets WholeField
open QuantumZipper (H)

section Reader

variable {Γ : Type*} [MeasurableSpace Γ]

/-- The retained-mean distribution reconstructed from countably many limits. -/
def retainedMeanReader (a : CoordJ → ℕ → Γ → ℝ) (γ : Γ) : DistOn upperHalfPlaneOpens :=
  pairJInv upperHalfPlaneOpens (fun c => limUnder atTop fun n => a c n γ)

theorem measurable_retainedMeanReader {a : CoordJ → ℕ → Γ → ℝ}
    (ha : ∀ c n, Measurable (a c n)) : Measurable (retainedMeanReader a) :=
  (measurable_pairJInv upperHalfPlaneOpens).comp (Measurable.of_eval fun c =>
    (StronglyMeasurable.limUnder fun n => (ha c n).stronglyMeasurable).measurable)

omit [MeasurableSpace Γ] in
/-- Limits on the countable determining family identify the entire random
distribution on one event of probability one. -/
theorem ae_eq_retainedMeanReader_of_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → Γ}
    {g : Ω → DistOn upperHalfPlaneOpens} {a : CoordJ → ℕ → Γ → ℝ}
    (hlim : ∀ c : CoordJ, ∀ᵐ ω ∂P, Tendsto (fun n => a c n (Y ω)) atTop
      (𝓝 (g ω (comb upperHalfPlaneOpens c)))) :
    g =ᵐ[P] retainedMeanReader a ∘ Y := by
  filter_upwards [ae_all_iff.2 hlim] with ω hω
  have heq : (fun c => limUnder atTop fun n => a c n (Y ω)) =
      pairJ upperHalfPlaneOpens (g ω) := funext fun c => (hω c).limUnder_eq
  dsimp only [Function.comp_apply, retainedMeanReader]
  rw [heq, pairJInv_pairJ]

end Reader

/-- Construct the local-set mean and its common history code from locality
and frozen-mean convergence on a countable family. The conditional means
include the actual retained-set germ and the history marks. -/
theorem exists_localSetMean_eq_retainedMeanReader
    {Ω Γ : Type*} [mΩ : MeasurableSpace Ω] [mΓ : MeasurableSpace Γ]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {Y : Ω → Γ} (hY : Measurable Y)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hloc : IsHistoryAvoidanceLocal (mΓ.comap Y) A h P)
    {a : CoordJ → ℕ → Γ → ℝ}
    (hlim : ∀ c : CoordJ, ∀ᵐ ω ∂P, Tendsto (fun n => a c n (Y ω)) atTop
      (𝓝 ((P[fun ω' => h ω' (comb upperHalfPlaneOpens c) |
        germSigma A h ⊔ mΓ.comap Y]) ω))) :
    ∃ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A h P g ∧
      g =ᵐ[P] retainedMeanReader a ∘ Y := by
  have hl : IsLocalSet A h P :=
    ((isLocalSet_tfae hh hA hAc).out 1 4).1 hloc.isAvoidanceLocal
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh hA hl
  refine ⟨g, hg, ae_eq_retainedMeanReader_of_tendsto fun c => ?_⟩
  filter_upwards [hlim c,
    ae_localSetMean_eq_condExp_history hh hA hY.comap_le hloc hAc hg
      (comb upperHalfPlaneOpens c)] with ω hω heq
  rw [heq]
  exact hω

end InteractingSLE.WFS
