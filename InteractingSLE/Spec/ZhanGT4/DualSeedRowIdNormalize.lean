/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdAxis
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdReciprocity
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformMartingale

/-!
# The actual source-reference cancellation for the seeded row

Packet PROVE-ZHAN-GT4-A22. The entrance formula subtracts precisely the
opposite source's fused partition function, leaving a first-prefix constant.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)

/-- A real alive original source has a nonzero centered real coordinate. -/
theorem source_centered_re_ne {W : ℝ → ℝ} (hW : Continuous W) {p T t : ℝ}
    {q : ℝ → ℂ} (hq : IsForwardSol W (p : ℂ) T q) (ht : t ∈ Icc (0 : ℝ) T) :
    (fwdMap W t p).re ≠ 0 :=
  re_ne_zero_of_im_eq_zero
    ((fwdMap_eq_of_isForwardSol hW hq ht).symm ▸ (hq.2 t ht).1) (fwdMap_real_im hW hq ht)

/-- The first entrance factor is exactly the original opposite reference
factor minus its fixed source normalization. -/
theorem seedSView_axis_eq_source_reference {n : ℕ} {κ S T t s : ℝ} (r : Fin n → ℝ)
    {W₁ W₂ : ℝ → ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} (V : Fin n → ℝ → ℝ)
    (hκ : κ ≠ 0) (h : OwnData W₁ (fwdHull W₂ t) (frzChart W₂ t) S (as t) (Ws t))
    (hW₂ : Continuous W₂) {q : ℝ → ℂ} (hq : IsForwardSol W₂ (0 : ℂ) T q)
    (ht : t ∈ Icc (0 : ℝ) T)
    {v : ℝ → ℂ} (hv : IsForwardSol (Ws t) ((W₂ t : ℝ) : ℂ) (as t S) v)
    (hV : ∀ m, V m 0 = 0) :
    dualGamma (16 / κ) (seedTView κ r W₁ W₂ bt Wt V s).seedAccessExponent *
        Real.log (deriv (fwdMap (fun u => W₂ u - W₂ 0) t) ((-W₂ 0 : ℝ) : ℂ)).re +
      (seedTView κ r W₁ W₂ bt Wt V s).seedAccessExponent *
        Real.log ((W₂ t - W₂ 0) - (seedTView κ r W₁ W₂ bt Wt V s).seedAccessSource (-W₂ 0) t) =
      (seedSView κ r W₁ W₂ as Ws V t).normEll 0 +
        (seedTView κ r W₁ W₂ bt Wt V s).seedAccessExponent * Real.log (W₂ 0) := by
  have ha := seedSView_normEll_zero r V hκ h hW₂ hq ht hv hV
  have hn : (fwdMap W₂ t 0).re ≠ 0 := by
    simpa only [Complex.ofReal_zero] using source_centered_re_ne hW₂ hq ht
  have hp : W₂ 0 ≠ 0 := by
    have h0 := source_centered_re_ne hW₂ hq ⟨le_rfl, ht.1.trans ht.2⟩
    simpa only [fwdMap_zero_eq_sub, Complex.zero_re, sub_re, ofReal_re, zero_sub, neg_ne_zero] using h0
  have he : ((frzChart W₂ t 0).re - W₂ t) / (-W₂ 0) =
      (-((fwdMap W₂ t 0).re)) / W₂ 0 := by
    simp only [frzChart, add_re, ofReal_re, add_sub_cancel_right, div_neg, neg_div]
  have hg : (W₂ t - W₂ 0) -
      (seedTView κ r W₁ W₂ bt Wt V s).seedAccessSource (-W₂ 0) t = -(fwdMap W₂ t 0).re := by
    rw [seedTView_source]
    simp only [frzChart, add_re, ofReal_re]
    ring
  rw [deriv_fwdMap_sub_const_source, hg, ha, he, Real.log_div (neg_ne_zero.2 hn) hp]
  dsimp only [seedTView, FrzData.seedAccessExponent]
  ring

namespace TwoViewRect
variable {n : ℕ} {κ S T : ℝ} {r : Fin n → ℝ} {W₁ W₂ : ℝ → ℝ}
  {as Ws bt Wt : ℝ → ℝ → ℝ} {V : Fin n → ℝ → ℝ}
  (h : TwoViewRect W₁ W₂ S T as Ws bt Wt)
include h

/-- The actual fused opposite logarithm differs from the normalized seeded
column logarithm by a constant depending on the first prefix alone. -/
theorem seed_fused_log_eq (hκ : κ ≠ 0) (hS : 0 < S) (hT : 0 < T)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) T)
    {q₁ q₂ : ℝ → ℂ} (hq₁ : IsForwardSol W₁ ((W₂ 0 : ℝ) : ℂ) S q₁)
    (hW₂ : Continuous W₂) (hq₂ : IsForwardSol W₂ (0 : ℂ) T q₂)
    (hV : ∀ m, V m 0 = 0)
    (hc : ∀ m, ∃ ρ > (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) T,
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull W₂ v))
    (hne : ∀ i, (seedSView κ r W₁ W₂ as Ws V t).gapVal i s ≠ 0) :
    (seedTView κ r W₁ W₂ bt Wt V s).seedAccessEll (-W₂ 0) t (W₂ t - W₂ 0) =
      (seedSView κ r W₁ W₂ as Ws V t).normEll s - (seedSView κ r W₁ W₂ as Ws V t).normEll 0 +
        ((seedSView κ r W₁ W₂ as Ws V 0).LT0 s +
          (seedSView κ r W₁ W₂ as Ws V 0).LS0 s (W₁ s)) +
        dualAlpha (16 / κ) * Real.log (deriv (fwdMap W₁ s) (W₂ 0)).re -
        (seedTView κ r W₁ W₂ bt Wt V s).seedAccessExponent * Real.log (W₂ 0) := by
  have hr := h.seed_raw_reciprocity (r := r) hκ hS hT hs ht hq₁ hc
  have hn := (seedSView κ r W₁ W₂ as Ws V t).normEll_eq_ell_of_gapVal_ne hne
  obtain ⟨S', _, h₁, v, hv⟩ := h.sOwn t ht
  have ha := seedSView_axis_eq_source_reference (s := s) (bt := bt) (Wt := Wt)
    r V hκ h₁ hW₂ hq₂ ht hv hV
  change (seedTView κ r W₁ W₂ bt Wt V s).ell t (W₂ t - W₂ 0) -
    dualGamma (16 / κ) (seedTView κ r W₁ W₂ bt Wt V s).seedAccessExponent *
      Real.log (deriv (fwdMap (fun u => W₂ u - W₂ 0) t) ((-W₂ 0 : ℝ) : ℂ)).re -
    (seedTView κ r W₁ W₂ bt Wt V s).seedAccessExponent *
      Real.log ((W₂ t - W₂ 0) - (seedTView κ r W₁ W₂ bt Wt V s).seedAccessSource (-W₂ 0) t) = _
  change (seedSView κ r W₁ W₂ as Ws V t).normEll s =
    (seedSView κ r W₁ W₂ as Ws V t).ell s (W₁ s) at hn
  linarith only [hr, hn, ha]

end TwoViewRect
end InteractingSLE.ZhanGT4
