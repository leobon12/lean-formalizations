/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqGeoWalls
import InteractingSLE.Spec.Sec7.R7GapEqGeoCorner
import InteractingSLE.Spec.Sec7.R7GapEqGeoGerms

/-!
# Finite outer and mixed physical gaps with the collars discharged

PROVE-R7-GAPEQ. The two-outer physical gap theorem now needs only global side order and
avoidance, besides the existing trace and first-visit data. In the mixed case the remaining
inputs are the one-barrier germ comparison and the local shared-corner geometry.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open QuantumZipper (H)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GapEqGeo

open WangWu Lemma71I PocketJordan PocketCoord Sec6 R7StopIn R7GapEq R7GapEqFin

/-- The actual two-outer finite change pocket has equal physical endpoints on every closed
gap. Both local collar hypotheses are proved; no attachment constancy or corner hypothesis
is used. Global side inclusion places the full outer exteriors inside the forbidden set. -/
theorem pocketGapEq_outerOuter {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hCl : changePocket R L r ⊆ leftSideOf (range R))
    (hCr : changePocket R L r ⊆ rightSideOf (range L)) {η : ℝ → ℂ} {F K : Set ℂ} {τ σ : ℝ}
    (hη : ContinuousOn η (Ici 0))
    (hsideR : negInv '' rightSideOf (range R) ⊆ F)
    (hsideL : negInv '' leftSideOf (range L) ⊆ F)
    (hK : frontier (cfPocket R L r) ⊆ K)
    (h42 : ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F) (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) : PocketGapEq η (cfPocket R L r) τ σ := by
  have hC := h.isCfPocket h0
  let O := cfArcR R L r '' Ioo (0 : ℝ) 1 ∪ cfArcL R L r '' Ioo (0 : ℝ) 1
  apply pocketGapEq_of_outerCollars hη hC.isOpen h42 havoid (O := O) ?_ ?_ hτ0 hτ hxf
  · rw [hC.frontier_eq]
    rintro p (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · by_cases hv0 : v = 0
      · exact Or.inl (Or.inl (congrArg (cfArcR R L r) hv0))
      by_cases hv1 : v = 1
      · exact Or.inl (Or.inr (congrArg (cfArcR R L r) hv1))
      exact Or.inr (Or.inl ⟨v, ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0),
        lt_of_le_of_ne hv.2 hv1⟩, rfl⟩)
    · by_cases hv0 : v = 0
      · exact Or.inl (Or.inl ((congrArg (cfArcL R L r) hv0).trans hC.junction))
      by_cases hv1 : v = 1
      · exact Or.inl (Or.inr ((congrArg (cfArcL R L r) hv1).trans hC.seed))
      exact Or.inr (Or.inr ⟨v, ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0),
        lt_of_le_of_ne hv.2 hv1⟩, rfl⟩)
  · rintro p (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact hasExteriorCollar_cfArcR h h0 hCl hsideR hK hv
    · exact hasExteriorCollar_cfArcL h h0 hCr hsideL hK hv

/-- The finite right-outer mixed pocket, with its exterior collar proved. The contained
left side's attachment and corner inputs can be supplied independently by the incident-germ
and local-extension theorems. No certified-frontier local clipping premise remains. -/
theorem pocketGapEq_rightOuter {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hCl : changePocket R L r ⊆ leftSideOf (range R)) {W : ℝ → ℝ} {η : ℝ → ℂ}
    {F K : Set ℂ} {τ σ : ℝ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hside : negInv '' rightSideOf (range R) ⊆ F) (hK : frontier (cfPocket R L r) ⊆ K)
    (h42 : ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ K)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hrev : R16.IsReverseVisitOrder (cfArcL R L r) fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcL R L r 1) (hτf : η τ ∉ η '' Ico 0 τ)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r) τ σ)
    (hcorner : ∀ t ∈ Ioo τ σ, firstVisit (fun s => η '' Icc 0 s) (cfArcL R L r) t < 1 →
      η t = cfArcL R L r 1 → HasOldAllowedCover η (cfPocket R L r) F K (η t) t) :
    PocketGapEq η (cfPocket R L r) τ σ := by
  have hC := h.isCfPocket h0
  have hA : IsClosed (cfArcR R L r '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hC.cont₁).isClosed
  have hdisj : ∀ v ∈ Ioo (0 : ℝ) 1, cfArcL R L r v ∉ cfArcR R L r '' Icc 0 1 := by
    rintro v hv ⟨u, hu, he⟩
    have hu0 : u ≠ 0 := fun hu0 => hv.1.ne' (hC.inj₂ ⟨hv.1.le, hv.2.le⟩
      ⟨le_rfl, zero_le_one⟩ (he.symm.trans (by rw [hu0, hC.junction])))
    have hu1 : u ≠ 1 := fun hu1 => hv.2.ne (hC.inj₂ ⟨hv.1.le, hv.2.le⟩
      ⟨zero_le_one, le_rfl⟩ (he.symm.trans (by rw [hu1, hC.seed])))
    exact hC.sides u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩ v hv he
  apply pocketGapEq_of_cornerCover hη hW hW0 hC.isOpen h42 hK havoid hA
    (by rw [hC.frontier_eq, union_comm]) hdisj ?_ hC.cont₂ hC.inj₂ hrev hτ0 hτ hτf hAC hcorner
  rintro p ⟨u, hu, rfl⟩ hpB
  have hu0 : u ≠ 0 := fun he => hpB ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [he, hC.junction]⟩
  have hu1 : u ≠ 1 := fun he => hpB ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [he, hC.seed]⟩
  exact hasExteriorCollar_cfArcR h h0 hCl hside hK
    ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩

/-- At an entrance which is the original seed, the shared-corner condition follows from the
source's no-return assertion. This case requires no extension past the original seed. -/
theorem cornerCover_of_seed_noReturn {η B : ℝ → ℂ} {C F K : Set ℂ} {τ σ : ℝ}
    (hτ0 : 0 ≤ τ) (hB : B 1 = 0) (hNR : ∀ t, 0 < t → η t ≠ 0) :
    ∀ t ∈ Ioo τ σ, firstVisit (fun s => η '' Icc 0 s) B t < 1 →
      η t = B 1 → HasOldAllowedCover η C F K (η t) t := by
  intro t ht _ heq
  exact False.elim (hNR t (hτ0.trans_lt ht.1) (heq.trans hB))

end InteractingSLE.Sec7.R7GapEqGeo
