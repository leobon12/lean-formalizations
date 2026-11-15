/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteFlow

/-!
# The other tip and separated-source gaps in the two views

Packet PROVE-ZHAN-GT4-A22. Uniqueness of boundary limits identifies the
other tip with the transposed image driver. Koebe's real-point estimate
then turns interval clearance and a derivative lower bound into a lower
bound for its distance from every seed image.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

namespace OwnData

/-- The other-tip value in one view is the final image driver in the other. -/
theorem frzImg_eq_transposed_driver {W₁ W₂ a W' a₂ W₂' : ℝ → ℝ} {T t t₂ : ℝ}
    (h : OwnData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W')
    (ht : t ∈ Icc (0 : ℝ) T)
    (h₂ : ImgData W₂ (fwdHull W₁ t) (fun z => fwdMap W₁ t z + W₁ t) t₂ a₂ W₂')
    {v : ℝ → ℂ} (hv : IsForwardSol W' (W₂ t₂ : ℂ) (a T) v) :
    frzImg W' a (W₂ t₂) t = W₂' (a₂ t₂) := by
  have hat := h.mapsTo_clock ht
  have hR : IsMapOut ((fun z => fwdMap W₂ t₂ z + W₂ t₂) '' fwdHull W₁ t)
      (fun z => fwdMap W' (a t) z + W' (a t)) := by
    rw [← h.img t ht]
    exact isMapOut_fwdMap_gen h.contW' hat.1
  have hlim := (h₂.rate t₂ ⟨h₂.pos.le, le_rfl⟩ _ hR).2.1
  have hlim' := (tendsto_fwdMap_of_isForwardSol h.contW' hat.1
    (isForwardSol_restrict hv hat.2)).add_const ((W' (a t) : ℝ) : ℂ)
  have hne : (𝓝[H] (W₂ t₂ : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have he := congrArg Complex.re (tendsto_nhds_unique hlim' hlim)
  simpa only [frzImg, Complex.add_re, Complex.ofReal_re,
    fwdMap_eq_of_isForwardSol h.contW' hv hat] using he

/-- A clear interval point with derivative at least `c` stays a definite
distance from the other image tip. -/
theorem le_abs_frzImg_sub_ownExt {W₁ W₂ a W' a₂ W₂' : ℝ → ℝ}
    {T t t₂ x r c : ℝ}
    (h : OwnData W₁ (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W')
    (ht : t ∈ Icc (0 : ℝ) T)
    (h₂ : ImgData W₂ (fwdHull W₁ t) (fun z => fwdMap W₁ t z + W₁ t) t₂ a₂ W₂')
    {v : ℝ → ℂ} (hv : IsForwardSol W' (W₂ t₂ : ℂ) (a T) v)
    (hr : 0 < r)
    (hclear : Disjoint (ball (x : ℂ) r)
      ((fun z => fwdMap W₁ t z + W₁ t) '' fwdHull W₂ t₂))
    (hc : c ≤ deriv (fun y : ℝ => (ownExt W₁ W' a
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) t y).re) x) :
    r / 96 * c ≤ |frzImg W' a (W₂ t₂) t -
      (ownExt W₁ W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) t x).re| := by
  have ht₂ : t₂ ∈ Icc (0 : ℝ) t₂ := ⟨h₂.pos.le, le_rfl⟩
  have hτ : 0 < a₂ t₂ := by
    have hh := h₂.mono (left_mem_Icc.2 h₂.pos.le) (right_mem_Icc.2 h₂.pos.le) h₂.pos
    rwa [h₂.a0] at hh
  have hcl : Disjoint (ball (x : ℂ) r) (fwdHull W₂' (a₂ t₂)) := by
    rwa [h₂.img t₂ ht₂]
  have hnot := notMem_ball_of_mem_closure hcl (start_mem_closure_fwdHull h₂.contW' hτ)
  have h0 : ∀ y : ℝ, (y : ℂ) ∈ ball (x : ℂ) (r / 2) → y ≠ W₂' 0 := by
    intro y hy he
    apply hnot
    rw [← he]
    exact ball_subset_ball (by linarith) hy
  obtain ⟨vx, hvx⟩ := exists_isForwardSol_of_disjoint_ball_gen h₂.contW'
    (h0 x (mem_ball_self (by positivity))) hτ.le hr hcl
  have hR : IsMapOut ((fun z => fwdMap W₁ t z + W₁ t) '' fwdHull W₂ t₂)
      (fun z => fwdMap W₂' (a₂ t₂) z + W₂' (a₂ t₂)) := by
    rw [← h₂.img t₂ ht₂]
    exact isMapOut_fwdMap_gen h₂.contW' hτ.le
  obtain ⟨hGd, -, -, -, -, hGR⟩ := h.ownExt_props ht hclear
  have hGe := hGR _ hR
  have hrl : 0 < r / 2 := by positivity
  have hGx := hGd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrl))
  have he := refl_eq_fwdMap_of_real h₂.contW' hτ.le hGd hGe (mem_ball_self hrl) hvx
  obtain ⟨δ, hδ, hlow, hxδ⟩ := exists_aliveDisc_self hvx hτ.le
  have hfx := (hasDerivAt_fwdMap_aliveDisc h₂.contW' hvx hδ hlow hxδ ⟨hτ.le, le_rfl⟩)
  have hde := deriv_eq_of_eq_upper hrl hGx (hfx.add_const _).differentiableAt he
    (fun ε hε => hGe (ConformalImageFull.mem_ball_inter_H hε.1 hε.2))
  rw [deriv_add_const] at hde
  have hreal := hGx.hasDerivAt.real_of_complex.deriv
  rw [hreal, hde] at hc
  have hkoebe := le_norm_fwdMap_real h₂.contW' hτ.le hr hcl h0
  have hlow' := (mul_le_mul_of_nonneg_left (hc.trans (Complex.re_le_norm _))
    (by positivity : 0 ≤ r / 96)).trans hkoebe
  rw [h.frzImg_eq_transposed_driver ht h₂ hv, he]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [show W₂' (a₂ t₂) - ((fwdMap W₂' (a₂ t₂) x).re + W₂' (a₂ t₂)) =
    -(fwdMap W₂' (a₂ t₂) x).re by ring, abs_neg]
  rw [abs_re_eq_norm.2 (fwdMap_real_im h₂.contW' hvx ⟨hτ.le, le_rfl⟩)]
  exact hlow'

end OwnData

end InteractingSLE.ZhanGT4
