/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxKer
import InteractingSLE.Spec.Supplement.GW2SpmPhys

/-!
# GW2's open lines: the local-set mean of the launch image is the launch transport of the union's mean

Packet PROVE-GW2-STAGEMEAN, R120 round. Under the conditional law `ν` of the earlier pieces, the launch image `A` of the
union is marked local for the coarsened marks `𝓜`, and given `𝓜` the centred launch field has the Gaussian kernel of
an explicit mean `m` (`GW2Omx.ae_launch_kernel`). A Gaussian conditional law given marks for which the set is marked
local identifies every local-set mean with its mean (`GW2Spm.ae_apply_eq_of_physLaw`):

* `ae_condExp_cexp_smul_of_rangeKerCF`: the kernel in `rangeKerCF` form at `r • ψ` is the Gaussian law at `r`;
* **`ae_localSetMean_eq_of_kernel`**: any local-set mean of `A` equals `m` in every pairing, almost surely.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Omx

open WholeField LocalSets

/-- **The kernel in `rangeKerCF` form, tested at `r • ψ`.** -/
theorem ae_condExp_cexp_smul_of_rangeKerCF {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {Q : Measure Ω} {h₀ m : Ω → DistOn upperHalfPlaneOpens} {V : Ω → Set ℂ}
    (hV : ∀ᵐ ω ∂Q, IsOpen (V ω) ∧ V ω ⊆ H)
    (hk : ∀ ψ : TestOn upperHalfPlaneOpens, Q[fun ω => Complex.exp (Complex.I * (h₀ ω ψ : ℂ)) | 𝓜] =ᵐ[Q]
      fun ω => rangeKerCF (m ω) (V ω) ψ) (ψ : TestOn upperHalfPlaneOpens) (r : ℝ) :
    ∀ᵐ ω ∂Q, Q[fun ω' => Complex.exp (Complex.I * ((r * h₀ ω' ψ : ℝ) : ℂ)) | 𝓜] ω =
      Complex.exp (Complex.I * ((r * m ω ψ : ℝ) : ℂ)) *
        ((Real.exp (-(1 / 2) * (r ^ 2 * zeroGFFTestCov (V ω) ψ ψ)) : ℝ) : ℂ) := by
  have e : (fun ω' => Complex.exp (Complex.I * ((r * h₀ ω' ψ : ℝ) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * (h₀ ω' (r • ψ) : ℂ)) := by
    funext ω'
    rw [map_smul, smul_eq_mul]
  rw [e]
  filter_upwards [hk (r • ψ), hV] with ω h1 h2
  rw [h1, rangeKerCF, map_smul, smul_eq_mul, zeroGFFTestCov_smul_self h2.1 h2.2, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **A Gaussian kernel given marks for which the set is marked local identifies its local-set means.** -/
theorem ae_localSetMean_eq_of_kernel {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (h𝓜 : 𝓜 ≤ mΩ) {h₀ m : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₀ ν) {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) (hAc : ∀ᵐ ω ∂ν, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hloc : IsHistoryAvoidanceLocal 𝓜 A h₀ ν)
    (hk : ∀ ψ : TestOn upperHalfPlaneOpens, ν[fun ω => Complex.exp (Complex.I * (h₀ ω ψ : ℂ)) | 𝓜] =ᵐ[ν]
      fun ω => rangeKerCF (m ω) (H \ A ω) ψ)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h₀ ν g) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂ν, g ω ψ = m ω ψ := by
  have hV : ∀ᵐ ω ∂ν, IsOpen (H \ A ω) ∧ H \ A ω ⊆ H := hAc.mono fun ω h => ⟨h.2, sdiff_subset⟩
  have h := GW2Spm.ae_apply_eq_of_physLaw hh hA h𝓜 hloc hAc hg ψ MeasurableSet.univ (m := fun ω => m ω ψ)
    fun r => (ae_condExp_cexp_smul_of_rangeKerCF hV hk ψ r).mono fun ω h _ => h
  filter_upwards [h] with ω hω
  exact hω (mem_univ ω)

end InteractingSLE.Theorem14.GW2Omx
