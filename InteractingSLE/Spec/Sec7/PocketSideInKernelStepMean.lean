/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInKernelStepTower
import InteractingSLE.Spec.Sec7.Lemma72CLocal

/-!
# The exact increment mean from a retained Gaussian kernel

PROVE-POCKET-SIDEIN. The retained Gaussian kernel supplies locality. Compare
its mean with the resulting germ mean using the equal-covariance theorem.
Countably many distributional generators make the equality simultaneous for
all tests. No germ-measurability assumption on the proposed mean is needed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets

/-- The mean of a retained kernel has a germ-measurable local-set version,
equal to the proposed mean as a whole distribution on one probability-one event. -/
theorem exists_localSetMean_eq_of_retained_kernel
    {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hℋ : ℋ ≤ mΩ)
    {A : Ω → Set ℂ} {h g : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[ℋ, hittingSigma] A) (hg : Measurable[ℋ] g)
    (hGerm : germSigma A h ≤ ℋ)
    (hRegular : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hHarmonic : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A ω))
    (hKernel : IsCondZeroBoundaryGFF P ℋ (fun ω => H \ A ω) (fun ω => h ω - g ω)) :
    ∃ g₀ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A h P g₀ ∧ g₀ =ᵐ[P] g := by
  have hLocal := Lemma72C.isLocalSet_of_isCondZeroBoundaryGFF
    hℋ hA hh.measurable hg hRegular hHarmonic hKernel
  obtain ⟨g₀, hg₀⟩ := IsLocalSet.exists_isLocalSetMean hh (hA.mono hℋ le_rfl) hLocal
  have hPair (φ : TestOn upperHalfPlaneOpens) : ∀ᵐ ω ∂P, g₀ ω φ = g ω φ := by
    have hCompare := ae_apply_eq_of_isCondZeroBoundaryGFF hGerm hℋ hh.measurable
      hg₀.1 hg hg₀.2.2 hKernel φ MeasurableSet.univ
      (fun _ => Eventually.of_forall fun _ _ => rfl)
    exact hCompare.mono fun ω hω => hω (mem_univ ω)
  refine ⟨g₀, hg₀, ?_⟩
  filter_upwards [ae_all_iff.2 fun j : ℕ × ℕ => hPair (LQGMetric.distGen upperHalfPlaneOpens j)]
    with ω hω
  exact LQGMetric.injective_distOn_pairings upperHalfPlaneOpens (funext hω)

end InteractingSLE.Sec7.PocketStopSide
