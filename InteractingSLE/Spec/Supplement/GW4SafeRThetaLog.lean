/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeREtaPhysical
import InteractingSLE.Spec.Supplement.GW4CLocChart
import InteractingSLE.Spec.Jordan.Coupling

/-! # GW4: actual analytic logarithms of the inherited component lifts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Topology
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix

/-- The frozen continuous argument of a component chart is the imaginary
part of an analytic derivative logarithm on its actual domain. -/
theorem isDomainChart_componentChart {R L C : Set ℂ} {c : Chart}
    (hch : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) :
    IsDomainChart C c := by
  have hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
  have hd : DifferentiableOn ℂ (deriv c.1) C := hch.1.deriv hCo
  let Lg : ℂ → ℂ := fun z => (Real.log ‖deriv c.1 z‖ : ℂ) + (c.2.2 z : ℂ) * Complex.I
  have hne := fun z (hz : z ∈ C) => CLoc.deriv_ne_zero_of_isComponentChart hch hCo hCH hz
  have hLc : ContinuousOn Lg C := by
    refine ContinuousOn.add ?_ ?_
    · exact Complex.continuous_ofReal.comp_continuousOn
        ((continuous_norm.comp_continuousOn hd.continuousOn).log fun z hz =>
          norm_ne_zero_iff.2 (hne z hz))
    · exact (Complex.continuous_ofReal.comp_continuousOn hch.2.2.2.2.2.1).mul continuousOn_const
  have hExp : ∀ z ∈ C, Complex.exp (Lg z) = deriv c.1 z := by
    intro z hz
    dsimp only [Lg]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.2 (hne z hz))]
    exact (hch.2.2.2.2.2.2 z hz).symm
  refine ⟨hc, GW3Joint.image_inv_eq_of_isComponentChart hch, Lg,
    ⟨differentiableOn_of_continuousOn_of_exp_eq hCo hLc hd hExp, hExp⟩, ?_⟩
  intro z _
  simp only [Lg, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]

/-- Every actual ambient component chart has the inherited analytic
logarithm required by R.5, including its source inversion branches. -/
theorem exists_derivLog_componentAmbientChart {R L C : Set ℂ} {c : Chart}
    (hch : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q) :
    ∃ Lg : ℂ → ℂ, IsDerivLog (componentAmbientChart c W q).1 Lg
      (componentAmbientChart c W q).dom ∧
      ∀ z ∈ (componentAmbientChart c W q).dom,
        (componentAmbientChart c W q).2.2 z = (Lg z).im := by
  have hBase := (isDomainChart_infinitySourceChart.trans
    (isDomainChart_componentChart hch hCo hCH)).trans isDomainChart_infinitySourceChart
  have hCur := hBase.trans (isDomainChart_loewner hW hW0 hq)
  rw [← Chart.loewner_eq_trans] at hCur
  change IsDomainChart _ (componentAmbientChart c W q) at hCur
  obtain ⟨Lg, hLg, hLift⟩ := hCur.2.2
  refine ⟨Lg, ?_, fun z hz => hLift (hCur.coe_dom ▸ hz)⟩
  rwa [hCur.coe_dom]

end InteractingSLE.Theorem14.GW4Fix
