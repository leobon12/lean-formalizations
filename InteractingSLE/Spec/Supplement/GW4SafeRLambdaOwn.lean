/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaFibres

/-! # GW4: finite exceptions for the actual component inverse accesses -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse

/-- Any finite physical exceptional set pulls back to a finite initial
component-coordinate exceptional set, simultaneously for all actual inverse
extensions. Thus excluding physical wall cut points is legitimate in the
full-fiber boundary-limit interface. -/
theorem Frame.exists_finite_own_access_exceptions {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {S : Set ℂ} (hS : S.Finite) :
    ∃ T : Set ℂ, T.Finite ∧ ∀ (R : ℝ → ℝ) (q : ℝ) (Fb : ℂ → ℂ),
      EqOn Fb (fwdMapInv R q) H → ContinuousOn Fb Hbar →
      MapsTo Fb H H → ∀ ξ : ℝ, extendFrom H (fwdMapInv R q) (ξ : ℂ) ∉ T →
      ∃ p : ℂ, p ∉ S ∧ Tendsto (componentAmbientChart F.c R q).2.1
        (𝓝[H] (ξ : ℂ)) (𝓝 p) := by
  obtain ⟨E, hE, hEc, -⟩ := Frame.exists_physical_inverse_extension hF hw
  refine ⟨Hbar ∩ E ⁻¹' S, Frame.finite_physical_inverse_preimage hF hw hE hEc hS, ?_⟩
  intro R q Fb hFb hFbc hFbH ξ hξ
  have hξbar : (ξ : ℂ) ∈ Hbar := by show 0 ≤ (ξ : ℂ).im; simp
  have hlim := Sec7.Aux29Cor.tendsto_inv_of_extension
    (c := Chart.id.loewner R q) hFb hFbc hξbar
  have hEq : extendFrom H (fwdMapInv R q) (ξ : ℂ) = Fb ξ := by
    apply extendFrom_eq
    · rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact hξbar
    · exact hlim
  have hFbbar : MapsTo Fb Hbar Hbar := by
    have hcl : closure H = Hbar := QuantumZipper.CA.Car.closure_H_eq_Hbar
    rw [← hcl] at hFbc ⊢
    exact hFbH.closure_of_continuousOn hFbc
  have hlimbar : Tendsto (fwdMapInv R q) (𝓝[H] (ξ : ℂ)) (𝓝[Hbar] (Fb ξ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall fun y hy =>
      hFb hy ▸ QuantumZipper.H_subset_Hbar (hFbH hy)⟩
  refine ⟨E (Fb ξ), fun h => hξ (hEq.symm ▸ ⟨hFbbar hξbar, h⟩), ?_⟩
  refine ((hEc _ (hFbbar hξbar)).tendsto.comp hlimbar).congr'
    (eventually_nhdsWithin_of_forall fun y hy => ?_)
  change E (fwdMapInv R q y) = relInvC F.c (fwdMapInv R q y)
  exact hE (hFb hy ▸ hFbH hy)

end InteractingSLE.Theorem14.GW4Fix
