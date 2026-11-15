/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessWitness
import InteractingSLE.Spec.Sec7.R7InfinityAccessAnchor

/-!
# Both compact inner-side conditions follow from the actual exterior geometry

PROVE-R7-GAPEQ. The exterior's real accesses determine its outer chart side.
A finite surviving outer-tail point then supplies the inner pocket witness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6 PocketJordan R7InfinityChart

/-- The proper two-arm pocket topology is symmetric in the arm labels. -/
theorem cfPocketInf_swap {C : Set ℂ} {A₁ A₂ : ℝ → ℂ} (hC : IsCfPocketInf C A₁ A₂) :
    IsCfPocketInf C A₂ A₁ := by
  refine ⟨hC.isOpen, hC.isConnected, hC.subset_H, ?_, hC.cont₂, hC.cont₁,
    hC.inj₂, hC.inj₁, hC.tendsto₂, hC.tendsto₁, hC.seed.symm, ?_, hC.mem_H₂, hC.mem_H₁, ?_⟩
  · rw [hC.frontier_eq, union_comm]
  · exact fun v hv w hw he => hC.sides w hw v hv he.symm
  · rw [hC.seed]; exact hC.mem_y

/-- The two former side-selection fields are proved from an untouched exterior
adhering to a real half-line and to the outer arm. -/
theorem infiniteFaceSides_of_exterior {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C E : Set ℂ} {τ s a q₁ q₂ : ℝ} {b₁ b₂ : ℝ → ℂ}
    (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0)
    (hrev : IsReverseVisitOrderInf A₁ fun t => η '' Icc 0 t)
    (hb₁ : IsLastVisitArm W η A₁ s a q₁ b₁) (hb₂ : IsLastVisitArm W η A₂ s a q₂ b₂)
    (ha : a < min q₁ q₂)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve
      (compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)))
    (hΓH : compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹) ⊆ Hbar)
    (hE : IsPreconnected E) (hEH : E ⊆ H) (hEb : ¬ IsBounded E)
    (havoid : Disjoint E (η '' Icc 0 s)) (hEC : E ⊆ (closure C)ᶜ)
    (houter : A₂ '' Ici 0 ⊆ closure E)
    (hreal : (∀ x : ℝ, 0 < x → (x : ℂ) ∈ closure E) ∨
      (∀ x : ℝ, x < 0 → (x : ℂ) ∈ closure E))
    (hloc : ∀ z ∈ frontier C, z ∈ H → IsLocConnWithin (closure C)ᶜ z) :
    InfiniteFaceSides W C s a (compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹)) := by
  have hs := hτ0.trans hτs
  have hED := subset_domain_of_not_isBounded hη hs hE hEH havoid hEb
  have haccess := compact_access_of_real_lift hb₁ hb₂ ha
    (exists_real_lift_outside_interval hη hW hW0 hs hED hreal a (max q₁ q₂))
  obtain ⟨-, hEO, hfr⟩ := compact_face_frontier_of_exterior_access hC hη hW hW0
    hτ0 hτs hτ hrev hb₁ hb₂ hE hEH hEb havoid hEC houter hΓ hΓH haccess
  have hbd := compactBoundary_mem_frontier hC hη hW hW0 hτ0 hτs hτ hb₁ hb₂
  have hy₂ : A₂ 0 ∈ η '' Icc 0 s := hC.seed ▸ ⟨τ, ⟨hτ0, hτs⟩, hτ⟩
  obtain ⟨hu, -, hD⟩ := lastVisit_tail_domain hη hs hC.cont₂ hC.tendsto₂ hC.mem_H₂ hy₂
  let v := lastVisit (fun t => η '' Icc 0 t) A₂ s + 1
  have huv : lastVisit (fun t => η '' Icc 0 t) A₂ s < v := lt_add_one _
  have hv : 0 < v := hu.trans_lt huv
  have hvD := hD v huv
  have hgH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hvD
  have hζH := (psiMap_mem_H_iff (fun he => not_mem_H_ofReal a (he ▸ hgH))).2 hgH
  have hζarm : psiMap a (fwdMap W s (A₂ v)) ∈ b₂ '' Ioo 0 1 :=
    hb₂.2.2.2.2.2.1 ▸ ⟨_, ⟨_, ⟨v, huv, rfl⟩, rfl⟩, rfl⟩
  have hζΓ : psiMap a (fwdMap W s (A₂ v)) ∈
      compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹) :=
    Or.inl (Or.inr (image_mono Ioo_subset_Icc_self hζarm))
  have he : trMap W 0 s (psiMapInv a (psiMap a (fwdMap W s (A₂ v)))) = A₂ v := by
    rw [psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hs hvD]
  refine ⟨hfr, exists_compact_inner_pocket_of_exterior_access hη hW hW0 hs hC.isOpen
    hΓ hΓH hbd hfr hζΓ hζH ?_ ?_⟩
  · rw [he]
    exact hloc _ (hC.frontier_eq.symm ▸ Or.inr ⟨v, hv.le, rfl⟩) (hC.mem_H₂ v hv)
  · rw [he]
    exact mem_closure_compact_exterior_access (houter ⟨v, hv.le, rfl⟩) hED hEC hEO

/-- An actual infinite pocket has a compactified component chart once its outer
exterior has the geometric properties proved for the ordered wall exteriors. -/
theorem exists_infiniteFaceChart_of_exterior {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C E : Set ℂ} {τ s : ℝ} (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0)
    (hrev : IsReverseVisitOrderInf A₁ fun t => η '' Icc 0 t)
    (hE : IsPreconnected E) (hEH : E ⊆ H) (hEb : ¬ IsBounded E)
    (havoid : Disjoint E (η '' Icc 0 s)) (hEC : E ⊆ (closure C)ᶜ)
    (houter : A₂ '' Ici 0 ⊆ closure E)
    (hreal : (∀ x : ℝ, 0 < x → (x : ℂ) ∈ closure E) ∨
      (∀ x : ℝ, x < 0 → (x : ℂ) ∈ closure E))
    (hloc : ∀ z ∈ frontier C, z ∈ H → IsLocConnWithin (closure C)ᶜ z) :
    ∃ (a : ℝ) (Γ : Set ℂ) (q : ℂ), R7EndFace.InfiniteFaceChart W C s a Γ q := by
  obtain ⟨q₁, q₂, hq⟩ := exists_pocket_chart_reduction hC hη hW hW0 hτ0 hτs hτ
  have ha : min q₁ q₂ - 1 < min q₁ q₂ := sub_one_lt _
  obtain ⟨b₁, b₂, hb₁, hb₂, hΓ, hΓH, -, -, hchart⟩ := hq _ ha
  have hsides := infiniteFaceSides_of_exterior hC hη hW hW0 hτ0 hτs hτ hrev hb₁ hb₂ ha
    hΓ hΓH hE hEH hEb havoid hEC houter hreal hloc
  obtain ⟨q, hq⟩ := hchart hsides
  exact ⟨_, _, q, hq⟩

end InteractingSLE.Sec7.R7InfinityAccess
