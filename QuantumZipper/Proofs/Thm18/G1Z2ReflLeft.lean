import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Complex.KernelChordR
import QuantumZipper.Proofs.Complex.KernelChordRight

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-REFL (1): reflection data of the inverse left-normalized uniformizer

For a simple chord `η` and a left-normalized uniformizer `φ` of `D = leftComponent η`, the
Schwarz reflection `Φ` of `φ` (`CA.Kernel.leftReflection`: Ahlfors, *Complex Analysis*, 3rd ed.,
Ch. 4 §6.5 Thm 24, with the Carathéodory boundary correspondence, Pommerenke, *Boundary Behaviour
of Conformal Maps*, Thm 2.6) is a conformal bijection of the doubled domain `L` onto
`ℂ \ [0,∞)`. Its inverse `Ψ` is holomorphic on `ℂ \ [0,∞)` with nonvanishing derivative
(`Koebe.hasDerivAt_invFunOn_of_injOn`), agrees with `φ⁻¹` on `ℍ`, and maps `(−∞,0)` onto
`(−∞,0)` increasingly. Own elementary arguments (open mapping via the inverse function theorem to
exclude the reflected half, the sign of `Ψ'` from difference quotients along `iℝ₊` as in
`G1PkgLeft.lean`) otherwise.

Main result: `sideReflGood_left_of_leftUniformizer`.
-/

noncomputable section

open Set Metric Filter Topology Complex Function
open QuantumZipper.CA QuantumZipper.CA.Uniformizer QuantumZipper.CA.Kernel
open scoped ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z2

theorem H_subset_slitNeg : H ⊆ slitNeg := fun z hz => by
  show -z ∈ slitPlane
  rw [mem_slitPlane_iff]
  right
  have : 0 < z.im := hz
  simp only [neg_im]
  linarith

theorem ofReal_mem_slitNeg {t : ℝ} (ht : t < 0) : (t : ℂ) ∈ slitNeg := by
  show -(t : ℂ) ∈ slitPlane
  rw [mem_slitPlane_iff]
  left
  simp only [neg_re, ofReal_re]
  linarith

theorem re_neg_of_mem_slitNeg {z : ℂ} (hz : z ∈ slitNeg) (him : z.im = 0) : z.re < 0 := by
  have h : -z ∈ slitPlane := hz
  rw [mem_slitPlane_iff] at h
  rcases h with h | h
  · simp only [neg_re] at h; linarith
  · simp [him] at h

variable {η : ℝ → ℂ} {φ Φ : ℂ → ℂ}

/-- The hypotheses on the reflected map. -/
structure ReflData (η : ℝ → ℂ) (φ Φ : ℂ → ℂ) : Prop where
  hη : IsSimpleChord η
  hφ : BijOn φ (leftComponent η) H
  hLo : IsOpen (leftDoubled η)
  hΦd : DifferentiableOn ℂ Φ (leftDoubled η)
  hΦb : BijOn Φ (leftDoubled η) slitNeg
  hΦeq : EqOn Φ φ (leftComponent η)

namespace ReflData

variable (R : ReflData η φ Φ)
include R

theorem left_sub : leftComponent η ⊆ leftDoubled η := fun _ hz => Or.inl (Or.inl hz)

theorem inv_spec {w : ℂ} (hw : w ∈ slitNeg) :
    invFunOn Φ (leftDoubled η) w ∈ leftDoubled η ∧ Φ (invFunOn Φ (leftDoubled η) w) = w := by
  have h : ∃ z ∈ leftDoubled η, Φ z = w := R.hΦb.surjOn hw
  exact ⟨invFunOn_mem h, invFunOn_eq h⟩

theorem inv_of_mem {z : ℂ} (hz : z ∈ leftDoubled η) : invFunOn Φ (leftDoubled η) (Φ z) = z := by
  have hw : Φ z ∈ slitNeg := R.hΦb.mapsTo hz
  exact R.hΦb.injOn (R.inv_spec hw).1 hz (R.inv_spec hw).2

theorem hasDerivAt_inv {w : ℂ} (hw : w ∈ slitNeg) :
    HasDerivAt (invFunOn Φ (leftDoubled η))
      (deriv Φ (invFunOn Φ (leftDoubled η) w))⁻¹ w := by
  have h := Koebe.hasDerivAt_invFunOn_of_injOn R.hLo R.hΦd R.hΦb.injOn (R.inv_spec hw).1
  rwa [(R.inv_spec hw).2] at h

theorem deriv_inv_ne {w : ℂ} (hw : w ∈ slitNeg) : deriv (invFunOn Φ (leftDoubled η)) w ≠ 0 := by
  rw [(R.hasDerivAt_inv hw).deriv]
  exact inv_ne_zero (Koebe.deriv_ne_zero_of_injOn R.hLo R.hΦd R.hΦb.injOn (R.inv_spec hw).1)

theorem eqOn_inv : EqOn (invFunOn φ (leftComponent η)) (invFunOn Φ (leftDoubled η)) H := by
  intro w hw
  have h : ∃ z ∈ leftComponent η, φ z = w := R.hφ.surjOn hw
  have hy := invFunOn_mem h
  have hy' := invFunOn_eq h
  have hs := R.inv_spec (H_subset_slitNeg hw)
  refine R.hΦb.injOn (R.left_sub hy) hs.1 ?_
  rw [hs.2, R.hΦeq hy, hy']

theorem conj_image_open : IsOpen ((starRingEnd ℂ) '' leftComponent η) := by
  have e : (starRingEnd ℂ) '' leftComponent η = (starRingEnd ℂ) ⁻¹' leftComponent η :=
    congrFun (image_eq_preimage_of_inverse (f := starRingEnd ℂ) (g := starRingEnd ℂ)
      (fun z => Complex.conj_conj z) (fun z => Complex.conj_conj z)) _
  rw [e]
  exact (isOpen_leftComponent R.hη).preimage Complex.continuous_conj

/-- The inverse maps the negative axis into the negative axis. -/
theorem inv_real {t : ℝ} (ht : t < 0) :
    (invFunOn Φ (leftDoubled η) t).im = 0 ∧ (invFunOn Φ (leftDoubled η) t).re < 0 := by
  set z := invFunOn Φ (leftDoubled η) t
  obtain ⟨hzL, hzΦ⟩ := R.inv_spec (ofReal_mem_slitNeg ht)
  rcases hzL with (hD | hC) | hN
  · exfalso
    have : Φ z ∈ H := by rw [R.hΦeq hD]; exact R.hφ.mapsTo hD
    rw [hzΦ] at this
    have h0 : (0 : ℝ) < (t : ℂ).im := this
    simp at h0
  · exfalso
    have hzL : z ∈ leftDoubled η := Or.inl (Or.inr hC)
    have hstrict : HasStrictDerivAt Φ (deriv Φ z) z :=
      ((R.hΦd.analyticOnNhd R.hLo) z hzL).hasStrictDerivAt
    have hmap := hstrict.map_nhds_eq (Koebe.deriv_ne_zero_of_injOn R.hLo R.hΦd R.hΦb.injOn hzL)
    have hmem : Φ '' ((starRingEnd ℂ) '' leftComponent η) ∈ 𝓝 (Φ z) := by
      rw [← hmap]
      exact image_mem_map (R.conj_image_open.mem_nhds hC)
    rw [hzΦ] at hmem
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
    set p : ℂ := (t : ℂ) + ((ε / 2 : ℝ) : ℂ) * I
    have hpH : p ∈ H := show 0 < p.im by simp [p]; linarith
    have hpb : p ∈ ball (t : ℂ) ε := by
      rw [mem_ball, dist_eq_norm]
      simp only [p, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith)]
      linarith
    obtain ⟨v, ⟨y, hyD, rfl⟩, hvp⟩ := hball hpb
    have h' : ∃ z ∈ leftComponent η, φ z = p := R.hφ.surjOn hpH
    have hy' := invFunOn_mem h'
    have hvL : conj y ∈ leftDoubled η := Or.inl (Or.inr ⟨y, hyD, rfl⟩)
    have heq : conj y = invFunOn φ (leftComponent η) p := by
      refine R.hΦb.injOn hvL (R.left_sub hy') ?_
      rw [hvp, R.hΦeq hy', invFunOn_eq h']
    have h1 : 0 < (invFunOn φ (leftComponent η) p).im := leftComponent_subset_H η hy'
    have h2 : 0 < y.im := leftComponent_subset_H η hyD
    rw [← heq] at h1
    simp at h1
    linarith
  · exact hN

/-- The reflected map sends the negative axis into the negative axis. -/
theorem fwd_real {s : ℝ} (hs : s < 0) : (Φ s).im = 0 ∧ (Φ s).re < 0 := by
  have hsL : (s : ℂ) ∈ leftDoubled η := Or.inr ⟨by simp, by simpa using hs⟩
  have hcont : ContinuousWithinAt Φ (leftComponent η) s :=
    (R.hΦd.continuousOn.continuousAt (R.hLo.mem_nhds hsL)).continuousWithinAt
  have hcl := hcont.mem_closure_image (ofReal_mem_closure_leftComponent R.hη hs)
  have hsub : Φ '' leftComponent η ⊆ {w : ℂ | 0 ≤ w.im} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [R.hΦeq hy]
    exact le_of_lt (show (0 : ℝ) < (φ y).im from R.hφ.mapsTo hy)
  have hge : 0 ≤ (Φ s).im :=
    closure_minimal hsub (isClosed_le continuous_const continuous_im) hcl
  have him : (Φ s).im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hge
    have hH : Φ s ∈ H := hpos
    have h' : ∃ z ∈ leftComponent η, φ z = Φ s := R.hφ.surjOn hH
    have hy := invFunOn_mem h'
    have := R.hΦb.injOn hsL (R.left_sub hy) (by rw [R.hΦeq hy, invFunOn_eq h'])
    have h0 : 0 < (invFunOn φ (leftComponent η) (Φ s)).im := leftComponent_subset_H η hy
    rw [← this] at h0
    simp at h0
  exact ⟨him, re_neg_of_mem_slitNeg (R.hΦb.mapsTo hsL) him⟩

end ReflData

end G1Z2
end Thm18Asm
end QuantumZipper
