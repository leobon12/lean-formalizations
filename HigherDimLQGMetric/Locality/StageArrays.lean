import HigherDimLQGMetric.Locality.FiniteArray
import HigherDimLQGMetric.Locality.StageScaled

/-! Finite dependent arrays of truncated internal metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

abbrev L7aFiniteArray {d : ℕ} {ι : Type}
    (S : Finset ι) (W : ι → TopologicalSpace.Opens (Rd d)) :=
  ∀ i : S,
    C((W i.1 : Set (Rd d)) × (W i.1 : Set (Rd d)), ℝ)

def l7a_stageArray {d : ℕ} {ι : Type}
    (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (S : Finset ι) (W : ι → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (g : DistRd d) : L7aFiniteArray S W := fun i =>
  internalC (l7a_truncScaledMetric hd κ hκ ξ hε g)
    (l7a_truncScaledMetric_isLength hd κ hκ ξ hε g)
    (W i.1).isOpen (hWc i.1 i.2)

theorem l7a_measurable_stageArray {d : ℕ} {ι : Type}
    (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (S : Finset ι) (W : ι → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d))) :
    Measurable (l7a_stageArray hd κ hκ ξ hε S W hWc) := by
  apply measurable_pi_iff.mpr
  intro i
  exact l7a_measurable_truncScaledInternal hd κ hκ ξ hε (W i.1)
    (hWc i.1 i.2)

theorem l7a_stageArray_sigma {d : ℕ} {ι Ω : Type}
    (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (S : Finset ι) (W : ι → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (g : Ω → DistRd d) :
    MeasurableSpace.comap
      (fun ω => l7a_stageArray hd κ hκ ξ hε S W hWc (g ω))
      inferInstance =
      ⨆ i ∈ S, MeasurableSpace.comap
        (fun ω => internalC
          (l7a_truncScaledMetric hd κ hκ ξ hε (g ω))
          (l7a_truncScaledMetric_isLength hd κ hκ ξ hε (g ω))
          (W i).isOpen (hWc i ‹i ∈ S›)) inferInstance := by
  rw [MeasurableSpace.comap_process_pi]
  rw [iSup_subtype']
  rfl

end HigherDimLQGMetric
