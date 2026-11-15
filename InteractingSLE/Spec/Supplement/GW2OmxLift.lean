/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Jordan.Chart
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# GW2's open lines: the lifts of two charts related by a dilation differ by a fixed multiple of `2π`

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start constant). For domain charts `c`, `d` of the same domain `D`
(open, preconnected) with `d.1 = λ · c.1` (`λ > 0`), `L_c + log λ` is a derivative-logarithm of `d.1`; two
derivative-logarithms on a preconnected open set differ by `2πi n` (`IsDerivLog.exists_int_eqOn`):

* **`lift_eq_add_of_dilation`**: `∃ n : ℤ, ∀ x ∈ D, d.2.2 x = c.2.2 x + 2π n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace InteractingSLE.Theorem14.GW2Omx

/-- **The lifts of two charts related by a dilation differ by a fixed multiple of `2π`.** -/
theorem lift_eq_add_of_dilation {D : Set ℂ} {c d : Chart} (hc : IsDomainChart D c) (hd : IsDomainChart D d)
    {lam : ℝ} (hlam : 0 < lam) (hdil : ∀ x ∈ D, d.1 x = (lam : ℂ) * c.1 x) :
    ∃ n : ℤ, ∀ x ∈ D, d.2.2 x = c.2.2 x + 2 * Real.pi * n := by
  have hDo : IsOpen D := hc.isOpen
  have hDc : IsPreconnected D := hc.isPreconnected
  have hcd := hc.differentiableOn_fwd
  obtain ⟨-, -, Lc, hLc, hcl⟩ := hc
  obtain ⟨-, -, Ld, hLd, hdl⟩ := hd
  have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hLc' : IsDerivLog d.1 (fun z => Lc z + Complex.log lam) D := by
    refine ⟨hLc.1.add_const _, fun z hz => ?_⟩
    have heq : d.1 =ᶠ[𝓝 z] fun x => (lam : ℂ) * c.1 x :=
      Filter.eventually_of_mem (hDo.mem_nhds hz) hdil
    have hdiff : DifferentiableAt ℂ c.1 z := (hcd z hz).differentiableAt (hDo.mem_nhds hz)
    rw [Complex.exp_add, hLc.2 z hz, Complex.exp_log hlam', heq.deriv_eq, deriv_const_mul _ hdiff]
    ring
  obtain ⟨n, hn⟩ := IsDerivLog.exists_int_eqOn hDo hDc hLd hLc'
  refine ⟨n, fun x hx => ?_⟩
  rw [hdl hx, hcl hx]
  show (Ld x).im = (Lc x).im + 2 * Real.pi * n
  rw [hn hx]
  have hlog : (Complex.log (lam : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hlam.le]
    exact Complex.ofReal_im _
  have h2 : ((2 : ℂ) * (Real.pi : ℂ) * I * (n : ℂ)).im = 2 * Real.pi * n := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) * I * (n : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [Complex.add_im, Complex.add_im, hlog, h2, add_zero]

end InteractingSLE.Theorem14.GW2Omx
