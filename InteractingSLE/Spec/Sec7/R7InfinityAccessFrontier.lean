/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessWalls

/-!
# Compact face frontier avoidance from one exterior access

PROVE-R7-GAPEQ. The contained arm's old prefix is visited. Its surviving tail is
on the compact boundary; the full outer arm is excluded by exterior adherence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6 PocketJordan R7InfinityChart

/-- Only a real exterior access outside the constructed boundary remains needed
to exclude every physical frontier point from the compact inner face. -/
theorem compact_face_frontier_of_exterior_access {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C E : Set ℂ} {τ s a q₁ q₂ : ℝ} {b₁ b₂ : ℝ → ℂ}
    (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0)
    (hrev : IsReverseVisitOrderInf A₁ fun t => η '' Icc 0 t)
    (hb₁ : IsLastVisitArm W η A₁ s a q₁ b₁) (hb₂ : IsLastVisitArm W η A₂ s a q₂ b₂)
    (hE : IsPreconnected E) (hEH : E ⊆ H) (hEb : ¬ IsBounded E)
    (havoid : Disjoint E (η '' Icc 0 s)) (hEC : E ⊆ (closure C)ᶜ)
    (houter : A₂ '' Ici 0 ⊆ closure E)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve
      (compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)))
    (hΓH : compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹) ⊆ Hbar)
    (haccess : ∃ x : ℝ, (x : ℂ) ∈ closure (psiMap a '' (fwdMap W s '' E)) ∧
      (x : ℂ) ∉ compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)) :
    let Γ := compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹);
    E ⊆ H \ fwdHull W s ∧ psiMap a '' (fwdMap W s '' E) ⊆ outerSide Γ ∧
      ∀ ζ ∈ innerSide Γ, trMap W 0 s (psiMapInv a ζ) ∉ frontier C := by
  have hs := hτ0.trans hτs
  have hED := subset_domain_of_not_isBounded hη hs hE hEH havoid hEb
  have hbd := compactBoundary_mem_frontier hC hη hW hW0 hτ0 hτs hτ hb₁ hb₂
  have hEO := compact_lift_exterior_subset_outerSide hW hW0 hs hΓ hΓH hE hED
    (fun ζ hζ hζH hzE => hEC hzE (frontier_subset_closure (hbd ζ hζ hζH))) haccess
  have hcl := compact_inner_not_mem_closure_exterior hW hW0 hs hΓ hΓH hEO
  have hy : A₁ 0 ∈ η '' Icc 0 s := ⟨τ, ⟨hτ0, hτs⟩, hτ⟩
  have hm := lastVisit_mem (R := fun t => η '' Icc 0 t) hC.cont₁ hC.tendsto₁
    (isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun _ ht => ht.1))
    ⟨0, self_mem_Ici, hy⟩
  refine ⟨hED, hEO, fun ζ hζ hfr => ?_⟩
  have hζH := innerSide_subset_H hΓ hΓH hζ
  have hwH := psiMapInv_mem_H (p := a) hζH
  have hzD := trMap_zero_mem_domain hW hW0 hs hwH
  rw [hC.frontier_eq] at hfr
  rcases hfr with ⟨v, hv, hvz⟩ | hz
  · by_cases huv : lastVisit (fun t => η '' Icc 0 t) A₁ s < v
    · have hg : psiMap a (fwdMap W s (A₁ v)) ∈ b₁ '' Ioo 0 1 :=
        hb₁.2.2.2.2.2.1 ▸ ⟨_, ⟨_, ⟨v, huv, rfl⟩, rfl⟩, rfl⟩
      rw [hvz, fwdMap_trMap_zero hW hW0 hs hwH, psiMap_psiMapInv] at hg
      exact innerSide_subset_compl hζ
        (Or.inl (Or.inl (image_mono Ioo_subset_Icc_self hg)))
    · have hvis := hrev s v hv _ hm.1 (le_of_not_gt huv) hm.2
      exact notMem_domain_of_mem_trace hη hs hvis (hvz ▸ hzD)
  · exact hcl ζ hζ (houter hz)

end InteractingSLE.Sec7.R7InfinityAccess
