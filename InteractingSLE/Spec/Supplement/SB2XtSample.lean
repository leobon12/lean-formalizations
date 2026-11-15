/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XsClause
import InteractingSLE.Spec.Supplement.SB2XlDom

/-!
# The per-stage correspondence at one sample, at the later relative stages

Packet PROVE-T14-SB2LIFT (round 27). At one sample with the bundle of `RelDriverAt''` (D7) and the upper launch chart,
for every relative stage `j ≥ 2` that launches with positive lifetime:

* **`StageFacts`**: the per-stage facts of PROVE-SB2-LIFTSET's v3 rule at stage `j` — B's (shifted) piece read in the
  relative chart is a driven curve `ρ = stCurvep …`, the relative driver generates its capacity trace up to its
  capacity lifetime, the relative facts `StageRelP`, the density of the good times and a positive shifted lifetime.
  At the concrete family these are LIFTSET's `StagesGeom3`, `StageOK` and the generation clause of
  `exists_EL_concrete3`, with the regularity of the relative piece;
* **`stageClause_of_facts`**: from them, the chain clause of `StageChainAtR2` at one stage (`stageClause`);
* **`stageChain_two`**: the full conclusion of `StageChainAtR2` at every such stage `j ≥ 2`: the matched actual launch
  (`actual_launch_of_bundles''`), the domain-chart clause (`isDomainChart_stage_of_bundles''`) and the chain clause
  (the lift through clustering, GEOM2's hull fields, the lifetime).
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

/-- **The per-stage facts of the v3 rule at one stage** (B's piece `e₁` from `s₁`, shifted by `t₀`; the relative stage
`e₂` from `s₂`). -/
def StageFacts (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (t₀ : ℝ≥0) (s₂ : ExplState) (e₂ : Drv) : Prop :=
  IsDrivenCurve (stCurvep c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂) ∧
  e₂.2 = capLife (stCurvep c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂) ∧
  (∀ T < capLife (stCurvep c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂),
    IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂))) ∧
  StageRelP c m (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀) s₂ e₂ ∧
  {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2 - t₀} ⊆ closure (goodTp c (fun t => pcPt s₁ e₁ (t₀ + t)) (e₁.2 - t₀)) ∧
  e₁.2 - t₀ ≠ 0 ∧ GW1P.PieceRegular e₂.1 e₂.2

/-- A launched piece of a boundary walk with regular launches is regular. -/
theorem pieceRegular_of_launch {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → Drv}
    (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) {k : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k = some (c, θ')) :
    GW1P.PieceRegular (D k).1 (D k).2 := by
  have h := hP k c θ' hl
  have hl' : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k ≠ none := by rw [hl]; simp
  rwa [GW1W.instrTime_walk hl', min_eq_right le_top] at h

variable {c : Chart} {m : ℝ} {s₁ s₂ : ExplState} {e₁ e₂ : Drv} {t₀ : ℝ≥0} {A Bp : Set ℂ}

/-- **The stage clause from the per-stage facts.** -/
theorem stageClause_of_facts (hℓ : IsDomainChart (H \ fillH Bp) (stChart s₁)) {Fℓ : ℂ → ℂ} {Cℓ : ℝ}
    (hFℓ : ∀ q ∈ Hbar, Tendsto (stChart s₁).2.1 (𝓝[H] q) (𝓝 (Fℓ q))) (hCℓ : ∀ q ∈ Hbar, ‖Fℓ q - q‖ ≤ Cℓ)
    (hc : c.IsConformal) {ĝ : ℂ → ℂ} {Cg : ℝ} (hĝ : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q)))
    (hCg : ∀ q ∈ Hbar, ‖ĝ q - q‖ ≤ Cg) (hc₁ : (stChart s₂).IsConformal) {F₁ : ℂ → ℂ} {C₁ : ℝ}
    (hF₁ : ∀ q ∈ Hbar, Tendsto (stChart s₂).2.1 (𝓝[H] q) (𝓝 (F₁ q))) (hC₁ : ∀ q ∈ Hbar, ‖F₁ q - q‖ ≤ C₁)
    (hmaps : ∀ y ∈ H, c.2.1 ((stChart s₂).2.1 y - (m : ℂ)) ∈ H \ fillH (A ∪ Bp))
    (hDX : IsDomainChart (H \ stageRetained (stChart s₁) (A ∪ Bp)) (stageRelChart (stChart s₁) c (stChart s₂) m))
    (hAB : IsCompact (A ∪ Bp)) (hpr₁ : GW1P.PieceRegular e₁.1 e₁.2) (ht₀ : (t₀ : ℝ≥0∞) ≤ e₁.2)
    (hpre : ∀ r ≤ t₀, LuM.trOf e₁ r ∉ H \ fillH (stageRetained (stChart s₁) (A ∪ Bp)))
    (hF : StageFacts c m s₁ e₁ t₀ s₂ e₂) :
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
      (∀ s : ℝ≥0, ((tL + s : ℝ≥0) : ℝ≥0∞) < e₁.2 →
        Tendsto (stageRelChart (stChart s₁) c (stChart s₂) m).2.1 (𝓝[H] (γ s)) (𝓝 (LuM.trOf e₁ (tL + s)))) ∧
      (∀ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < e₁.2 →
        ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
          (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) →
            Wr r = e₂.1 r.toNNReal ∧ ηr r = LuM.trOf e₂ r.toNNReal) ∧
          IsSB2RelChain (stageRetained (stChart s₁) (A ∪ Bp)) (stageRelChart (stChart s₁) c (stChart s₂) m)
            (LuM.trOf e₁) γ tL (S₀ : ℝ) Wr ηr) ∧
      e₂.2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < e₁.2),
        ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)) := by
  obtain ⟨hρ, he₂, hgen, hrel, hdense, hL0, hpr₂⟩ := hF
  exact stageClause hℓ hFℓ hCℓ hc hĝ hCg hc₁ hF₁ hC₁ hmaps hDX hAB hpr₁ ht₀ hpre hρ he₂ hgen hrel hdense hpr₂ hL0

/-- At head time `0` the head condition of the hull fields is vacuous. -/
theorem hpre_zero (hpr₁ : GW1P.PieceRegular e₁.1 e₁.2) (X : Set ℂ) :
    ∀ r ≤ (0 : ℝ≥0), LuM.trOf e₁ r ∉ H \ X := by
  intro r hr hmem
  have hr0 : r = 0 := le_antisymm hr bot_le
  rw [hr0, (LuM.isGeneratingTrace_trOf hpr₁).1] at hmem
  have h0 : (0 : ℝ) < (0 : ℂ).im := hmem.1
  simp at h0

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
  {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}

/-- **The per-stage correspondence at one sample at every launching relative stage `j ≥ 2` of positive lifetime**,
from the bundle of `RelDriverAt''` and the per-stage facts. -/
theorem stageChain_two (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputs κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ ⊤ → (D₁ k).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧ lHit (stChart (ExplState.run
          κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ) (hβ0 : β₀ 0 = 0)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o)
    {A : Set ℂ} {ĝ : ℂ → ℂ} {Cg : ℝ} (hc : IsDomainChart (H \ fillH A) c) (hA : IsCompact A)
    (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) (hCg : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ Cg)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hhead : β₀ '' Icc 0 tL ⊆ hullK A)
    (hfacts : ∀ j, 2 ≤ j → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      (D₂ j).2 ≠ 0 →
      StageFacts c m (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)) (D₁ (j + o)) 0
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j) (D₂ j)) :
    ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ), 2 ≤ j →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j = some (c₁, θ') → (D₂ j).2 ≠ 0 →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o + 1)).2.2.2.1 (j + o) ≠ none ∧
      IsDomainChart (H \ stageRetained (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
          (A ∪ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
        (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))) c c₁ m) ∧
      ∃ (tL' : ℝ≥0) (γ' : ℝ≥0 → ℂ),
        (∀ s : ℝ≥0, ((tL' + s : ℝ≥0) : ℝ≥0∞) < (D₁ (j + o)).2 →
          Tendsto (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))) c c₁
            m).2.1 (𝓝[H] (γ' s)) (𝓝 (LuM.trOf (D₁ (j + o)) (tL' + s)))) ∧
        (∀ S₀ : ℝ≥0, ((tL' + S₀ : ℝ≥0) : ℝ≥0∞) < (D₁ (j + o)).2 →
          ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
            (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ' r.toNNReal) (S₀ : ℝ) →
              Wr r = (D₂ j).1 r.toNNReal ∧ ηr r = LuM.trOf (D₂ j) r.toNNReal) ∧
            IsSB2RelChain (stageRetained (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
                (A ∪ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
              (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))) c c₁ m)
              (LuM.trOf (D₁ (j + o))) γ' tL' (S₀ : ℝ) Wr ηr) ∧
        (D₂ j).2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL' + S₀ : ℝ≥0) : ℝ≥0∞) < (D₁ (j + o)).2),
          ENNReal.ofReal (capClock (fun r : ℝ => γ' r.toNNReal) (S₀ : ℝ)) := by
  intro j c₁ θ' hj hl hz
  have hl' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none := by
    rw [hl]; simp
  have hl₁ := actual_launch_of_bundles'' hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS j hl' hz
  have hdom := isDomainChart_stage_of_bundles'' hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS
    hc hA hĝ hCg hγ hhead j c₁ θ' hj hl hz
  refine ⟨hl₁, hdom, ?_⟩
  -- the data of the stage
  obtain ⟨⟨c₀, θ₀⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
  have hnot₁ := WalkIntRunChron.not_done_of_launch _ D₁ hl₁'
  have hnot₂ := WalkIntRunChron.not_done_of_launch _ D₂ hl
  obtain ⟨-, -, hc₁⟩ := eq_launch_of_launches (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hl
  subst hc₁
  have hℓ := Lw.isDomainChart_runChart (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ (j + o) hnot₁
  have h₁ := Lw.isDomainChart_runChart (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hR.reg₂ j hnot₂
  have hB := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ (j + o) hnot₁
  have hRelEq := prefix_lift_of_bundles'' hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS j hj hl'
  have hRel := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hR.reg₂ j hnot₂
  have hRelH : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j ⊆ Hbar := by
    rw [hRelEq]
    rintro _ ⟨s, -, rfl⟩
    exact hγp.2.2.1 s
  have hk₁ := (GW1W.even_of_launches_walk hl₁).2
  have hBr : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o) ⊆ range β₀ := by
    rw [hC.range_eq]
    exact prefix_subset_physSet D₁ (n := j + o) hk₁.le
  have hcl : IsClosed (β₀ '' Ici tL) := (isClosedEmbedding_of_isProperCurve hβp).isClosedMap _ isClosed_Ici
  have hmaps := mapsTo_stage_of_lift hc h₁ hA hĝ hCg hRel hRelH hγ hβp.1 hRelEq hB hBr hhead hcl
  obtain ⟨Fℓ, Cℓ, hFℓ, hCℓ⟩ := (GW1P.isClosed_pieces_run (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ (j + o)).1
  obtain ⟨F₁, C₁, hF₁, hC₁⟩ := (GW1P.isClosed_pieces_run (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hR.reg₂ j).1
  have hpr₁ := pieceRegular_of_launch hP₁ hl₁'
  exact stageClause_of_facts hℓ hFℓ hCℓ hc.1 hĝ hCg h₁.1 hF₁ hC₁ hmaps hdom (hA.union hB) hpr₁ bot_le
    (hpre_zero hpr₁ _) (hfacts j hj hl' hz)

end InteractingSLE.Theorem14.SB.Mn
