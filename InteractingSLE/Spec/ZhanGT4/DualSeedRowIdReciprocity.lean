/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdFactors

/-!
# Reciprocity from the actual seeded two-view geometry

Packet PROVE-ZHAN-GT4-A22. All common factor identities are discharged
by the actual tip maps, protected integrated seeds and the rectangle identity
for the Schwarzian integral.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)
/-- The first reference partition function depends on the first prefix alone. -/
theorem seedSView_reference_independent
    {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) (W₁ W₂ : ℝ → ℝ)
    (as Ws : ℝ → ℝ → ℝ) (V : Fin n → ℝ → ℝ) (s t : ℝ) :
    (seedSView κ r W₁ W₂ as Ws V t).LT0 s +
        (seedSView κ r W₁ W₂ as Ws V t).LS0 s (W₁ s) =
      (seedSView κ r W₁ W₂ as Ws V 0).LT0 s +
        (seedSView κ r W₁ W₂ as Ws V 0).LS0 s (W₁ s) := rfl

namespace TwoViewRect
variable {n : ℕ} {κ S T : ℝ} {r : Fin n → ℝ} {W₁ W₂ : ℝ → ℝ}
  {as Ws bt Wt : ℝ → ℝ → ℝ} {V : Fin n → ℝ → ℝ}
  (h : TwoViewRect W₁ W₂ S T as Ws bt Wt)
include h

/-- Actual raw-log reciprocity. No common-factor equalities are assumptions. -/
theorem seed_raw_reciprocity (hκ : κ ≠ 0) (hS : 0 < S) (hT : 0 < T)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) T)
    {q : ℝ → ℂ} (hq : IsForwardSol W₁ ((W₂ 0 : ℝ) : ℂ) S q)
    (hc : ∀ m, ∃ ρ > (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) T,
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull W₂ v)) :
    (seedTView κ r W₁ W₂ bt Wt V s).ell t (W₂ t - W₂ 0) =
      (seedSView κ r W₁ W₂ as Ws V t).ell s (W₁ s) +
        ((seedSView κ r W₁ W₂ as Ws V 0).LT0 s +
          (seedSView κ r W₁ W₂ as Ws V 0).LS0 s (W₁ s)) +
        dualAlpha (16 / κ) * Real.log (deriv (fwdMap W₁ s) (W₂ 0)).re := by
  obtain ⟨S', hSS', h₁, q₁, hq₁⟩ := h.sOwn t ht
  have hs' : s ∈ Icc (0 : ℝ) S' := ⟨hs.1, hs.2.trans hSS'⟩
  have hG : (deriv (fwdMap W₁ s) (W₂ 0)).re ≠ 0 :=
    (deriv_fwdMap_real h₁.cont hq hs).2.ne'
  have hD : frzImgD (Ws t) (as t) (W₂ t) s ≠ 0 :=
    (deriv_fwdMap_real h₁.contW' hq₁ (h₁.mapsTo_clock hs')).2.ne'
  have hf := h.seed_tip_factors (κ := κ) (r := r) (V := V) hs ht
  have hm := h.seed_mark_factors (κ := κ) (r := r) hS hT hs hc
  have hd21 : (seedSView κ r W₁ W₂ as Ws V t).A21 s ≠ 0 := div_ne_zero hD hG
  have hF1 : (seedTView κ r W₁ W₂ bt Wt V s).F 1 t (W₂ t - W₂ 0) =
      (seedSView κ r W₁ W₂ as Ws V t).A21 s * (deriv (fwdMap W₁ s) (W₂ 0)).re := by
    rw [hf.2.1]
    exact (div_mul_cancel₀ _ hG).symm
  have he := seed_access_log_reciprocity_translated
    (seedSView κ r W₁ W₂ as Ws V t) (seedTView κ r W₁ W₂ bt Wt V s)
    hκ rfl rfl hf.1 hF1 hf.2.2.1 hf.2.2.2 (fun m => ((hm m).2 t ht).1)
    (fun m => ((hm m).2 t ht).2) (h.mono hs ht).frzLogF_eq.symm hd21 hG
  exact he

end TwoViewRect
end InteractingSLE.ZhanGT4
