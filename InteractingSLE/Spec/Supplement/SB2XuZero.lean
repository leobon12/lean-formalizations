/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XtSample

/-!
# The per-stage correspondence at one sample, at the relative root of a piece start

Packet PROVE-T14-SB2LIFT (round 27). At a piece start (`PieceStartV` at offset `o`, D7; the start piece may be the
last, infinite one) the relative root is B's start piece read from its visit time `t₀` of `R`. At one sample:

* the relative root's chart is the identity (`ExplState.init 0`), so its prefix is the real point `0` and B's prefix
  before `o` (on the head of `β₀`, `PieceStartV.head`) lifts into `{0}`; the domain-chart clause and the inclusion of
  the relative domain follow from `isDomainChart_stage_of_lift` / `mapsTo_stage_of_lift` with that lift image;
* **`hpre_of_head`**: if the start piece is in the hull of the upper prefix up to `t₀` (its head part), then its stage
  trace up to `t₀` is in the retained set (the head condition of the hull fields);
* **`stageChain_zero`**: the full conclusion of `StageChainAtR2` at the root, from the per-stage facts at stage `0`
  with the shift `t₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk LuM GW1W GW1Bookkeep Sec7.PocketTraversal Sec7.Lemma71C
open FinRel (IsSB2RelChain)

/-- **The head condition of the hull fields from the head of the start piece**: if B's piece is in the hull of the
upper prefix up to `t₀`, its stage trace up to `t₀` avoids the complement of the retained set. -/
theorem hpre_of_head {s₁ : ExplState} {e₁ : Drv} {A Bp : Set ℂ} {t₀ : ℝ≥0}
    (hℓ : IsDomainChart (H \ fillH Bp) (stChart s₁))
    (hhead : ∀ r ≤ t₀, pcPt s₁ e₁ r ∈ hullK A)
    (hfX : fillH (stageRetained (stChart s₁) (A ∪ Bp)) = stageRetained (stChart s₁) (A ∪ Bp)) :
    ∀ r ≤ t₀, LuM.trOf e₁ r ∉ H \ fillH (stageRetained (stChart s₁) (A ∪ Bp)) := by
  intro r hr hmem
  rw [hfX] at hmem
  obtain ⟨hH, hnot⟩ := hmem
  have hpc : pcPt s₁ e₁ r = (stChart s₁).2.1 (LuM.trOf e₁ r) :=
    LuM.bdVal_eq_of_mem_H hℓ.1.1.continuousOn hH
  have hpH : pcPt s₁ e₁ r ∈ H := by rw [hpc]; exact hℓ.1.2.1 hH
  have hA : pcPt s₁ e₁ r ∈ fillH A := by
    rcases hhead r hr with h | ⟨x, -, hx⟩
    · exact h
    · exfalso
      have h0 : (0 : ℝ) < (pcPt s₁ e₁ r).im := hpH
      rw [← hx] at h0
      simp at h0
  refine hnot ⟨hH, ?_⟩
  rw [← hpc]
  exact fillH_mono subset_union_left hA

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
  {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o : ℕ} {c : Chart} {m : ℝ}

/-- **The per-stage correspondence at one sample at the relative root of a piece start**, from the per-stage facts at
stage `0` (shift `t₀`) and the head of the start piece. -/
theorem stageChain_zero (hP : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβp : Supp9B.IsProperCurve β₀) (hβinj : Function.Injective β₀)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    {A : Set ℂ} {ĝ : ℂ → ℂ} {Cg : ℝ} (hc : IsDomainChart (H \ fillH A) c) (hA : IsCompact A)
    (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) (hCg : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ Cg)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hhead : β₀ '' Icc 0 tL ⊆ hullK A) {t₀ : ℝ≥0}
    (ht₀ : (t₀ : ℝ≥0∞) ≤ (D₁ o).2)
    (hstart : ∀ r ≤ t₀, pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o) r ∈ hullK A)
    (hF : StageFacts c m (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o) t₀
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 0) (D₂ 0)) :
    ∀ (c₁ : Chart) (θ' : ℝ),
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (0 + 1)).2.2.2.1 0 = some (c₁, θ') →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none ∧
      IsDomainChart (H \ stageRetained (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o))
          (A ∪ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o))
        (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) c c₁ m) ∧
      ∃ (tL' : ℝ≥0) (γ' : ℝ≥0 → ℂ),
        (∀ s : ℝ≥0, ((tL' + s : ℝ≥0) : ℝ≥0∞) < (D₁ o).2 →
          Tendsto (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) c c₁
            m).2.1 (𝓝[H] (γ' s)) (𝓝 (LuM.trOf (D₁ o) (tL' + s)))) ∧
        (∀ S₀ : ℝ≥0, ((tL' + S₀ : ℝ≥0) : ℝ≥0∞) < (D₁ o).2 →
          ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
            (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ' r.toNNReal) (S₀ : ℝ) →
              Wr r = (D₂ 0).1 r.toNNReal ∧ ηr r = LuM.trOf (D₂ 0) r.toNNReal) ∧
            IsSB2RelChain (stageRetained (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o))
                (A ∪ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o))
              (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) c c₁ m)
              (LuM.trOf (D₁ o)) γ' tL' (S₀ : ℝ) Wr ηr) ∧
        (D₂ 0).2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL' + S₀ : ℝ≥0) : ℝ≥0∞) < (D₁ o).2),
          ENNReal.ofReal (capClock (fun r : ℝ => γ' r.toNNReal) (S₀ : ℝ)) := by
  intro c₁ θ' hl
  have hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
    rw [hP.launch, launches_launch, Function.update_self]; simp
  refine ⟨hl₁, ?_⟩
  obtain ⟨⟨c₀, θ₀⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
  have hnot₁ := WalkIntRunChron.not_done_of_launch _ D₁ hl₁'
  obtain ⟨-, -, hc₁⟩ := eq_launch_of_launches (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hl
  subst hc₁
  -- the relative root's chart is the identity
  have hrun0 : ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 0 = ExplState.init 0 := rfl
  have hch : stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 0) = Chart.id.recenter 0 := by
    rw [hrun0]; rfl
  -- B's prefix before `o` lifts into `{0}`
  set Bp := SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o with hBp
  set Rel := liftImage β₀ tL γ Bp with hRel
  have hRel0 : Rel ⊆ {0} := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hts⟩ := hP.head hs
    have h1 : tL + s = t := hβinj hts.symm
    have h2 : s = 0 := by
      have : tL + s ≤ tL := h1 ▸ ht
      exact le_antisymm (by simpa using this) bot_le
    rw [h2, hγ.2.2.1]
    rfl
  have hRelf : fillH Rel = ∅ := YuanCharacterisation.fillH_eq_empty_of_subset fun z hz => by
    rw [hRel0 hz]; simp
  have hRelc : IsCompact Rel := (Set.subsingleton_singleton.anti hRel0).isCompact
  have hRelH : Rel ⊆ Hbar := fun z hz => by
    rw [hRel0 hz]; show (0 : ℝ) ≤ (0 : ℂ).im; simp
  have h₁ : IsDomainChart (H \ fillH Rel) (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 0)) := by
    rw [hRelf, sdiff_empty, hch, Chart.recenter_zero]
    exact isDomainChart_id
  have hℓ := Lw.isDomainChart_runChart (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ o hnot₁
  have hB := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ o hnot₁
  have hk₁ := (GW1W.even_of_launches_walk hl₁).2
  have hBr : Bp ⊆ range β₀ := by
    rw [hβr]
    exact prefix_subset_physSet D₁ (n := o) hk₁.le
  have hcl : IsClosed (β₀ '' Ici tL) := (isClosedEmbedding_of_isProperCurve hβp).isClosedMap _ isClosed_Ici
  have hdom := isDomainChart_stage_of_lift hℓ hc h₁ hA hĝ hCg hRelc hRelH hγ hβp.1 rfl hB hBr hhead hcl
  have hmaps := mapsTo_stage_of_lift hc h₁ hA hĝ hCg hRelc hRelH hγ hβp.1 rfl hB hBr hhead hcl
  refine ⟨hdom, ?_⟩
  obtain ⟨Fℓ, Cℓ, hFℓ, hCℓ⟩ := (GW1P.isClosed_pieces_run (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ o).1
  obtain ⟨F₁, C₁, hF₁, hC₁⟩ := GW1P.hasProperBdryExt_recenter_id 0
  have hc₁ : (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 0)).IsConformal := by
    rw [hch]; exact Chart.isConformal_id.recenter 0
  rw [← hch] at hF₁
  have hpr₁ := pieceRegular_of_launch hP₁ hl₁'
  obtain ⟨-, -, -, hfX⟩ := retained_facts hℓ hFℓ hCℓ (hA.union hB) hdom
  exact stageClause_of_facts hℓ hFℓ hCℓ hc.1 hĝ hCg hc₁ hF₁ hC₁ hmaps hdom (hA.union hB) hpr₁ ht₀
    (hpre_of_head hℓ hstart hfX) hF

end InteractingSLE.Theorem14.SB.Mn
