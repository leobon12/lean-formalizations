/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6LandTip
import InteractingSLE.Spec.Sec7.FanTipFiber

/-!
# R.6: transfer of the singleton current tip through the incident face

PROVE-R6-LANDING; Astra's `r6_face_geometry`, Section 4, ruling R98.
The inverse of the incident-face uniformizer is injective on the closed
half-plane and identifies the relative and ambient driver coordinates.
Consequently the ambient singleton tip fibre transfers to the relative
one, and the driver-collar lemma gives physical local containment.
This uses the singleton property at the current tip only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec7.R6Land

/-- A boundary-injective incident-face factor transfers the ambient
singleton current tip to the relative chart. The factor fixes zero
because both inverse maps use centered driving coordinates. -/
theorem singleton_tip_fibre_of_factorization {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) (hsingle : IsSingletonTipFiber W T)
    {E L : ℂ → ℂ} (hL : MapsTo L Hbar Hbar) (hLi : InjOn L Hbar) (hL0 : L 0 = 0)
    (hfac : ∀ z ∈ Hbar, E z = extendFrom H (fwdMapInv W T) (L z)) :
    ∀ x : ℝ, E (x : ℂ) = E 0 → x = 0 := by
  intro x hx
  have h0 : (0 : ℂ) ∈ Hbar := R6Fc.real_mem_Hbar 0
  have hxH : (x : ℂ) ∈ Hbar := R6Fc.real_mem_Hbar x
  have heq : extendFrom H (fwdMapInv W T) (L (x : ℂ)) = loewnerTip W T := by
    rw [← hfac _ hxH, hx, hfac _ h0, hL0]
    rfl
  have htip : loewnerTip W T = η T := hη.loewnerTip_eq hW hW0 hT
  have htipnot : η T ∉ H \ fwdHull W T := by
    intro h
    apply h.2
    rw [hη.2.2 T hT]
    exact ⟨h.1, Or.inl (subset_closure ⟨T, ⟨hT, le_rfl⟩, rfl⟩)⟩
  have hLreal : (L (x : ℂ)).im = 0 := by
    refine le_antisymm ?_ (hL hxH)
    by_contra h
    have hLH : L (x : ℂ) ∈ H := not_le.1 h
    have hmem := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hLH
    have hext := extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 hT) hLH
    rw [← hext, heq, htip] at hmem
    exact htipnot hmem
  have hLre : L (x : ℂ) = ((L (x : ℂ)).re : ℂ) :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using hLreal)
  have hre : (L (x : ℂ)).re = 0 := hsingle _ (by rwa [← hLre])
  have hz : L (x : ℂ) = L 0 := by rw [hLre, hre, Complex.ofReal_zero, hL0]
  have hx0 : (x : ℂ) = 0 := hLi hxH h0 hz
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using hx0)

/-- The two-outer physical containment step of the note follows from
Aux. 136 and the common-time incident-face factorization. Multiple
prime ends at the subsequently chosen exposed landing are allowed. -/
theorem driver_collar_physical_of_factorization
    {C P V : Set ℂ} {O : Chart} {vL vR : ℝ}
    (M : R6Tn.BoundaryChart C P O vL vR) (hVO : V ⊆ (O.dom : Set ℂ))
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hsingle : IsSingletonTipFiber W T)
    {L : ℂ → ℂ} (hL : MapsTo L Hbar Hbar) (hLi : InjOn L Hbar) (hL0 : L 0 = 0)
    (hfac : ∀ z ∈ Hbar, M.inverse z = extendFrom H (fwdMapInv W T) (L z))
    {r : ℝ} (hr : 0 < r) (hcol : H ∩ ball (0 : ℂ) r ⊆ O.1 '' V) :
    ∃ e > 0, (O.dom : Set ℂ) ∩ ball (M.inverse 0) e ⊆ V :=
  driver_collar_physical M hVO
    (singleton_tip_fibre_of_factorization hη hW hW0 hT hsingle hL hLi hL0 hfac) hr hcol

end InteractingSLE.Sec7.R6Land
