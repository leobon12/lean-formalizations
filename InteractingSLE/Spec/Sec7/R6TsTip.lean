/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrLanding

/-!
# Aux. 136 identifies the two-outer driver prime end

PROVE-R6-TWO, Astra §§2.5 and 4.2 (R98). The two-outer case has the
singleton ambient current-tip fibre. Consequently the boundary
factorization and the physical current-tip identity identify the
driver prime end, without a separate normalization hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Ts

/-- The singleton ambient current tip fixes the driver normalization of
an incident face factor. Injectivity of that factor is not needed here. -/
theorem driver_zero_of_ambient_factorization
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hs : IsSingletonTipFiber W t) {E L : ℂ → ℂ}
    (hL : MapsTo L Hbar Hbar) (hE0 : E 0 = η t)
    (hfactor0 : E 0 = extendFrom H (fwdMapInv W t) (L 0)) :
    L 0 = 0 :=
  R6Tr.singletonTipFiber_full hη hW hW0 ht hs _
    (hL (R6Fc.real_mem_Hbar 0)) (hfactor0.symm.trans hE0)

/-- Transport the singleton tip to the relative inverse. The former
`L 0 = 0` input is now proved from Aux. 136 and the actual physical tip. -/
theorem singleton_tip_of_ambient_factorization_of_tip
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hs : IsSingletonTipFiber W t) {E L : ℂ → ℂ}
    (hL : MapsTo L Hbar Hbar) (hLi : InjOn L Hbar) (hE0 : E 0 = η t)
    (hfactor : ∀ x : ℝ, E (x : ℂ) = extendFrom H (fwdMapInv W t) (L x)) :
    ∀ x : ℝ, E (x : ℂ) = η t → x = 0 := by
  have hL0 := driver_zero_of_ambient_factorization hη hW hW0 ht hs hL hE0
    (by simpa only [Complex.ofReal_zero] using hfactor 0)
  exact R6Tr.singleton_tip_of_ambient_factorization hη hW hW0 ht hs hL hLi hL0 hfactor

/-- The two-outer exposed-point choice needs an ambient driver collar
and a Jordan face factorization. Its own landing fibre is unrestricted. -/
theorem exists_negative_exposed_landing_of_face_factorization
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hs : IsSingletonTipFiber W t) {D D₀ U : Set ℂ}
    (hD : D ⊆ H \ fwdHull W t) {r : ℝ} (hr : 0 < r)
    (hcollar : H ∩ ball (0 : ℂ) r ⊆ (fwdMapInv W t) ⁻¹' D₀)
    {E L : ℂ → ℂ} (hE : ContinuousOn E Hbar) (hE0 : E 0 = η t)
    (hL : MapsTo L Hbar Hbar) (hLi : InjOn L Hbar)
    (hfactor : ∀ x : ℝ, E (x : ℂ) = extendFrom H (fwdMapInv W t) (L x))
    (hU : IsOpen U) (hpU : η t ∈ U) {v : ℝ} (hv : v < 0) :
    ∃ ξ : ℝ, v < ξ ∧ ξ < 0 ∧ E (ξ : ℂ) ∈ U ∧ E (ξ : ℂ) ≠ η t ∧
      ∃ e > 0, D ∩ ball (E (ξ : ℂ)) e ⊆ D₀ := by
  exact R6Tr.exists_negative_exposed_landing_of_ambient_collar hη hW hW0 ht hs
    hD hr hcollar hE hE0
    (singleton_tip_of_ambient_factorization_of_tip hη hW hW0 ht hs hL hLi hE0 hfactor)
    hU hpU hv

end InteractingSLE.Sec7.R6Ts
