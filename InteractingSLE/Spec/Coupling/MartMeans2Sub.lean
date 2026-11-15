/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.Pushforward
import SupercriticalConformalCovariance.ZBConformal.Covariance

/-!
# A conformal chart restricted to a subdomain

Packet PROVE-CPL-MART2, part (2), deterministic tool. For a conformal chart `c = (fwd, inv, lift)` (PROVE-PUSHFWD's
`Chart.IsConformal`) and an open `O ⊆ ℍ` (in the application `O = ℍ \ K_τ`), `inv` is a conformal bijection of `O`
onto the open set `inv '' O` (`IsConformal.isConformalBijection_sub`), and for a test function `φ` supported in `O`
the transported test function `pushTest φ = 1_U |fwd′|² (φ ∘ fwd)` is the conformal transport of `φ|_O` to `inv '' O`
(`IsConformal.coe_pushTest_eq_confPushTest`). Hence:

* `IsConformal.tsupport_pushTest_subset_image`: `supp (pushTest φ) ⊆ inv '' O`;
* `IsConformal.zeroGFFTestCov_pushTest_sub`: `‖pushTest φ‖²_{H⁻¹(inv '' O)} = ‖φ‖²_{H⁻¹(O)}` (conformal invariance of
  the Dirichlet energy, SupercriticalConformalCovariance's `zeroGFFTestCov_conformal`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H isOpen_H zeroGFFTestCov)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)

namespace InteractingSLE

namespace Chart

variable {c : Chart} {O : Opens ℂ}

/-- `inv '' O = U ∩ fwd⁻¹(O)` for `O ⊆ ℍ`. -/
theorem IsConformal.image_eq_inter_preimage (hc : c.IsConformal) {O : Set ℂ} (hO : O ⊆ H) :
    c.2.1 '' O = (c.dom : Set ℂ) ∩ c.1 ⁻¹' O := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hc.inv_mem_dom (hO hw), by rw [mem_preimage, hc.2.2 w (hO hw)]; exact hw⟩
  · rintro ⟨hz, hzO⟩
    exact ⟨c.1 z, hzO, hc.inv_fwd hz⟩

/-- The image of an open subset of `ℍ` under `inv` is open. -/
theorem IsConformal.isOpen_image_of_subset (hc : c.IsConformal) {O : Set ℂ} (hOo : IsOpen O) (hO : O ⊆ H) :
    IsOpen (c.2.1 '' O) := by
  rw [hc.image_eq_inter_preimage hO]
  exact hc.differentiableOn_fwd.continuousOn.isOpen_inter_preimage c.dom.isOpen hOo

/-- The image `inv '' O`, as an open set (the interior keeps it open for every chart; for a conformal chart and
`O ⊆ ℍ` it is `inv '' O`, `IsConformal.coe_imageOpens`). -/
def imageOpens (c : Chart) (O : Opens ℂ) : Opens ℂ :=
  ⟨interior (c.2.1 '' O), isOpen_interior⟩

theorem IsConformal.coe_imageOpens (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H) :
    (c.imageOpens O : Set ℂ) = c.2.1 '' O :=
  (hc.isOpen_image_of_subset O.isOpen hO).interior_eq

theorem IsConformal.imageOpens_subset_H (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H) :
    (c.imageOpens O : Set ℂ) ⊆ H := by
  rw [hc.coe_imageOpens hO]
  exact (image_mono hO).trans hc.2.1.image_subset

/-- `inv` is a conformal bijection of `O ⊆ ℍ` onto `inv '' O`. -/
theorem IsConformal.isConformalBijection_sub (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H) :
    IsConformalBijection c.2.1 (O : Set ℂ) (c.imageOpens O : Set ℂ) :=
  ⟨hc.1.mono hO, by rw [hc.coe_imageOpens hO]; exact (hc.injOn.mono hO).bijOn_image⟩

/-- On `inv '' O`, the inverse function of `inv|_O` is `fwd`. -/
theorem IsConformal.invFunOn_sub_eq (hc : c.IsConformal) {O : Set ℂ} (hO : O ⊆ H) {z : ℂ}
    (hz : z ∈ c.2.1 '' O) : Function.invFunOn c.2.1 O z = c.1 z := by
  obtain ⟨w, hw, rfl⟩ := hz
  rw [(hc.injOn.mono hO).leftInvOn_invFunOn hw, hc.2.2 w (hO hw)]

/-- A test function on `ℍ` supported in `O`, as a test function on `O`. -/
def testOnSub (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ O) : TestOn O :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩

@[simp]
theorem coe_testOnSub (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ O) :
    ⇑(testOnSub φ hφ) = ⇑φ :=
  rfl

/-- **The transported test function of a test function supported in `O`** is the conformal transport of its
restriction to `O` along `inv : O → inv '' O`. -/
theorem IsConformal.coe_pushTest_eq_confPushTest (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H)
    (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ O) :
    ⇑(pushTest hc φ) = ⇑(confPushTest (hc.isConformalBijection_sub hO) (testOnSub φ hφ)) := by
  funext z
  change _ = (c.imageOpens O : Set ℂ).indicator (fun y => ‖deriv (Function.invFunOn c.2.1 (O : Set ℂ)) y‖ ^ 2 *
    φ (Function.invFunOn c.2.1 (O : Set ℂ) y)) z
  rw [hc.coe_imageOpens hO]
  by_cases hz : z ∈ c.2.1 '' (O : Set ℂ)
  · have hzU : z ∈ c.dom := by
      rw [← SetLike.mem_coe, hc.coe_dom]
      exact image_mono hO hz
    rw [indicator_of_mem hz, pushTest_apply_of_mem hc φ hzU, hc.invFunOn_sub_eq hO hz]
    have he : Function.invFunOn c.2.1 (O : Set ℂ) =ᶠ[𝓝 z] c.1 :=
      Filter.eventuallyEq_of_mem ((hc.isOpen_image_of_subset O.isOpen hO).mem_nhds hz) fun y hy =>
        hc.invFunOn_sub_eq hO hy
    rw [he.deriv_eq]
  · rw [indicator_of_notMem hz]
    by_cases hzU : z ∈ c.dom
    · rw [pushTest_apply_of_mem hc φ hzU]
      have hfz : c.1 z ∉ tsupport φ := fun h => hz ⟨c.1 z, hφ h, hc.inv_fwd hzU⟩
      rw [image_eq_zero_of_notMem_tsupport hfz, mul_zero]
    · exact pushTest_apply_of_notMem hc φ hzU

/-- The transported test function of a test function supported in `O ⊆ ℍ` is supported in `inv '' O`. -/
theorem IsConformal.tsupport_pushTest_subset_image (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H)
    (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ O) :
    tsupport (pushTest hc φ) ⊆ c.2.1 '' (O : Set ℂ) := by
  rw [hc.coe_pushTest_eq_confPushTest hO φ hφ, ← hc.coe_imageOpens hO]
  exact (confPushTest (hc.isConformalBijection_sub hO) (testOnSub φ hφ)).tsupport_subset

/-- **Conformal invariance of the Dirichlet energy on a subdomain**: for `φ` supported in `O ⊆ ℍ`,
`‖pushTest φ‖²_{H⁻¹(inv '' O)} = ‖φ‖²_{H⁻¹(O)}`. -/
theorem IsConformal.zeroGFFTestCov_pushTest_sub (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H)
    (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ O) :
    zeroGFFTestCov (c.2.1 '' (O : Set ℂ)) (pushTest hc φ) (pushTest hc φ) = zeroGFFTestCov O φ φ := by
  rw [hc.coe_pushTest_eq_confPushTest hO φ hφ, ← hc.coe_imageOpens hO]
  exact SupercriticalConformalCovariance.ZBConformal.zeroGFFTestCov_conformal
    (hc.isConformalBijection_sub hO) _ _

end Chart

end InteractingSLE
