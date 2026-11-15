/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QwChart
import InteractingSLE.Spec.Supplement.WalkMarkedLocal
import InteractingSLE.Spec.Supplement.WalkInfLaunch
import InteractingSLE.Spec.Supplement.WalkSideSpec
import InteractingSLE.Spec.Supplement.GW1Bookkeep
import InteractingSLE.Spec.Supplement.GW1ActiveRun
import InteractingSLE.Spec.Supplement.GW1Connector
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-!
# The terminal hull identity of the step `ℓ → ℓ + 2`: the stage sets, and the identity from the hulls before it

Worker REVIEW-FABLE-T14 (items 2–3 of PROVE-SB2-LCMEAN's handoff R13.8). The relative versions of B's stage `ℓ`
(F2b′'s successor, `Na.SB2LowerStageVersionStatement3`) give the retained hull at every B-time `t` before the piece's
lifetime as `K ∪ c⁻¹(K_{a t})` (`c` the canonical hull chart, `a` the relative clock). The retained hull after the
piece is the fill of the stage set through the connector `ℓ + 1`. Two facts relate them:

* **the stage sets** (`stageSet_capSpec_subset`, `stageSet_succ_succ_subset`): B's capped stage set at any B-time lies
  in the stage set through the connector, and every point of the latter in `ℍ` lies in the stage set before `ℓ` or in
  the capped stage set at a rational time before the piece's lifetime — the piece's tip at its lifetime is its real
  end point (`GW1Bookkeep.PieceSimpleAt`), and the connector adds no point of `ℍ`;
* **the identity from below** (`fill_eq_stepHull_of_cover`): a filled set `Z = fill S` containing the old hull, whose
  points of `S` in `ℍ` are covered by sets `X i` with `X i ∩ ℍ = K ∪ c⁻¹(K_{a i})`, `X i ⊆ Z`, the times `a i ≤ T`
  cofinal in `[0, T)`, is `K ∪ c⁻¹(K_T)` (by capacity, `Qw.hull_eq_of_cofinal`).

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Qx

open Exist Exist.Staged Exist.StagedLaw WalkSide GW1Bookkeep Qw

/-! ### The identity from below -/

theorem stepHull_mono {K : Set ℂ} {x₀ : ℝ} {W : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) :
    stepHull K x₀ W s ⊆ stepHull K x₀ W t := by
  refine union_subset_union_right _ (image_mono fun z hz => ⟨hz.1, ?_⟩)
  exact hz.2.trans (ENNReal.ofReal_le_ofReal hst)

/-- **The terminal hull identity from the hulls before the lifetime.** -/
theorem fill_eq_stepHull_of_cover {K S : Set ℂ} (hK : IsHPHull K) (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hZ : IsHPHull (fillH S)) (hKZ : K ⊆ fillH S) {ι : Type*} {D : Set ι}
    {X : ι → Set ℂ} {a : ι → ℝ} (ha : ∀ i ∈ D, 0 ≤ a i ∧ a i ≤ T)
    (hX : ∀ i ∈ D, X i ∩ H = stepHull K x₀ W (a i)) (hXZ : ∀ i ∈ D, X i ⊆ fillH S)
    (hcov : S ∩ H ⊆ K ∪ ⋃ i ∈ D, X i) (hcof : ∀ s, 0 ≤ s → s < T → ∃ i ∈ D, s ≤ a i) :
    fillH S = stepHull K x₀ W T := by
  have hXT := isHPHull_stepHull hK x₀ hW hW0 hT
  refine hull_eq_of_cofinal hK x₀ hW hW0 hT hZ ?_ hKZ fun s hs hsT => ?_
  · refine fillH_subset_of_inter_H_subset hXT fun z hz => ?_
    rcases hcov hz with hzK | hzX
    · exact Or.inl hzK
    · simp only [mem_iUnion, exists_prop] at hzX
      obtain ⟨i, hi, hzi⟩ := hzX
      have hzi' : z ∈ X i ∩ H := ⟨hzi, hz.2⟩
      rw [hX i hi] at hzi'
      exact stepHull_mono (ha i hi).2 hzi'
  · obtain ⟨i, hi, hsi⟩ := hcof s hs hsT
    refine ⟨a i, (ha i hi).1, hsi, ?_⟩
    rw [← hX i hi]
    exact inter_subset_left.trans (hXZ i hi)

/-! ### B's stage sets around a piece -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {θ : ℝ}

/-- The walk's instruction at a launching stage is the flow for all time. -/
theorem walk_instr_of_launch {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    (boundaryWalkSpec b jumps θ true).2.2[ℓ]? = some (Sum.inl (θ, ⊤)) ∧
      ℓ < (boundaryWalkSpec b jumps θ true).2.2.length := by
  obtain ⟨hev, hk⟩ := GW1W.even_of_launches_walk hl
  refine ⟨?_, hk⟩
  rw [GW1Conn.getElem?_boundaryWalkSpec]
  simp only [hk, hev, ↓reduceIte]

/-- The connector after a launching stage launches nothing. -/
theorem walk_noLaunch_succ {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1 + 1)).2.2.2.1 (ℓ + 1) = none := by
  by_contra h
  obtain ⟨hev, -⟩ := GW1W.even_of_launches_walk h
  obtain ⟨hev', -⟩ := GW1W.even_of_launches_walk hl
  omega

/-- The tip set of a `PieceSimpleAt` piece stopped at any `S ≤ ζ` is the boundary image of its trace on `[0, S]`. -/
theorem tipSet_eq_image_of_pieceSimpleAt {c : Chart} {W : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {old : Set ℂ} {q₀ q₁ : ℝ}
    (hS : PieceSimpleAt c W ζ old q₀ q₁) :
    ∃ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ), (ζ ≠ ⊤ → f (α ζ.toNNReal) = (q₁ : ℂ)) ∧
      ∀ S : ℝ≥0∞, S ≤ ζ →
        c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S = f '' (α '' {t | (t : ℝ≥0∞) ≤ S}) := by
  obtain ⟨f, α, C, hf, -, -, hW0, hWc, hgen, -, -, -, hEnd, -⟩ := hS
  refine ⟨f, α, hEnd, fun S hSζ => ?_⟩
  have hgen' : IsGeneratingTrace W S α := by
    have := WalkInf.isGeneratingTrace_min hgen S
    rwa [min_eq_left hSζ] at this
  have hWc' : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S} := hWc.mono fun t ht => le_trans ht hSζ
  refine CounterflowRange.tipSet_stopped_eq_of_tendsto hgen' hWc' hW0 fun t ht => hf _ ?_
  exact Sec7.IsGeneratingTrace.mem_Hbar hgen'
    (hWc'.mono fun s (hs : (s : ℝ≥0∞) < S) => (show (s : ℝ≥0∞) ≤ S from hs.le)) hW0 ht

variable (κ b jumps) in
/-- The piece of the capped program at stage `ℓ`, for the walk launching at `ℓ`. -/
theorem pieceSet_capSpec_eq {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ} {ω : Ω} {τ : ℝ≥0∞}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    WalkLaw.pieceSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ τ) E ℓ ω =
      ((ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) ℓ).2.2.2.2.1.tipSet
        (fun r : ℝ≥0 => (E ℓ ω).1 (min (r : ℝ≥0∞) (min τ (E ℓ ω).2)).toNNReal) (min τ (E ℓ ω).2)) ∩ H := by
  obtain ⟨hwℓ, hlen⟩ := walk_instr_of_launch hl
  have hlaunch := launches_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) (τ := τ) hlen.le hwℓ
    (fun j => E j ω)
  have hl' : (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ τ) (fun j => E j ω)
      (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hlaunch]; exact hl
  unfold WalkLaw.pieceSet
  simp only [hl', ↓reduceIte]
  rw [run_capSpec_of_le hlen.le _ le_rfl, instrTime_capSpec hlen.le]

variable (κ b jumps) in
/-- The walk's piece at a launching stage `ℓ`. -/
theorem pieceSet_walk_eq {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ} {ω : Ω}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    WalkLaw.pieceSet κ b jumps (boundaryWalkSpec b jumps θ true) E ℓ ω =
      ((ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) ℓ).2.2.2.2.1.tipSet
        (fun r : ℝ≥0 => (E ℓ ω).1 (min (r : ℝ≥0∞) (E ℓ ω).2).toNNReal) (E ℓ ω).2) ∩ H := by
  have ht := GW1WalkExit.instrTime_walk_of_launch hl
  unfold WalkLaw.pieceSet
  simp only [hl, ↓reduceIte]
  rw [ht, min_eq_right le_top]

variable (κ b jumps) in
/-- **B's capped stage set at any time lies in the stage set through the connector.** -/
theorem stageSet_capSpec_subset {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ} {ω : Ω} {old : Set ℂ} {q₀ q₁ : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hS : PieceSimpleAt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) ℓ).2.2.2.2.1
      (E ℓ ω).1 (E ℓ ω).2 old q₀ q₁) (τ : ℝ≥0∞) :
    WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ τ) E (ℓ + 1) ω ⊆
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps θ true) E (ℓ + 2) ω := by
  obtain ⟨-, hlen⟩ := walk_instr_of_launch hl
  obtain ⟨f, α, -, himg⟩ := tipSet_eq_image_of_pieceSimpleAt hS
  rw [WalkLaw.stageSet_succ, WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, pieceSet_capSpec_eq κ b jumps hl]
  rw [show ℓ + 2 = ℓ + 1 + 1 from rfl, WalkLaw.stageSet_succ, WalkLaw.stageSet_succ, pieceSet_walk_eq κ b jumps hl]
  rintro z (hz | ⟨hzt, hzH⟩)
  · exact Or.inl (Or.inl hz)
  · refine Or.inl (Or.inr ⟨?_, hzH⟩)
    have h1 := himg (min τ (E ℓ ω).2) (min_le_right _ _)
    have h2 := himg (E ℓ ω).2 le_rfl
    rw [h1] at hzt
    rw [h2]
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hzt
    exact ⟨_, ⟨s, (show (s : ℝ≥0∞) ≤ (E ℓ ω).2 from le_trans hs (min_le_right _ _)), rfl⟩, rfl⟩

variable (κ b jumps) in
/-- **The stage set through the connector is covered by the capped stage sets before the lifetime**: its points
(all in `ℍ`) lie in the stage set before `ℓ` or in the capped stage set at a rational time before the piece's
lifetime; the tip at the lifetime is the real end point, and the connector launches nothing. -/
theorem stageSet_succ_succ_subset {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ} {ω : Ω} {old : Set ℂ} {q₀ q₁ : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hS : PieceSimpleAt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) ℓ).2.2.2.2.1
      (E ℓ ω).1 (E ℓ ω).2 old q₀ q₁) :
    WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps θ true) E (ℓ + 2) ω ⊆
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps θ true) E ℓ ω ∪
        ⋃ (q : ℚ) (_ : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < (E ℓ ω).2),
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ (Real.toNNReal q : ℝ≥0)) E
            (ℓ + 1) ω := by
  obtain ⟨-, hlen⟩ := walk_instr_of_launch hl
  obtain ⟨f, α, hend, himg⟩ := tipSet_eq_image_of_pieceSimpleAt hS
  have hno : WalkLaw.pieceSet κ b jumps (boundaryWalkSpec b jumps θ true) E (ℓ + 1) ω = ∅ := by
    unfold WalkLaw.pieceSet
    simp only [walk_noLaunch_succ hl, ↓reduceIte]
  rw [show ℓ + 2 = ℓ + 1 + 1 from rfl, WalkLaw.stageSet_succ, WalkLaw.stageSet_succ, hno, union_empty,
    pieceSet_walk_eq κ b jumps hl]
  rintro z (hz | ⟨hzt, hzH⟩)
  · exact Or.inl hz
  rw [himg (E ℓ ω).2 le_rfl] at hzt
  obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hzt
  rcases (show (s : ℝ≥0∞) ≤ (E ℓ ω).2 from hs).lt_or_eq with hlt | heq
  · obtain ⟨q, hq0, hsq, hqζ⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    refine Or.inr (mem_iUnion₂.2 ⟨q, hqζ, ?_⟩)
    rw [WalkLaw.stageSet_succ, pieceSet_capSpec_eq κ b jumps hl]
    refine Or.inr ⟨?_, hzH⟩
    rw [himg _ (min_le_right _ _)]
    exact ⟨_, ⟨s, (show (s : ℝ≥0∞) ≤ min _ _ from le_min hsq.le hs), rfl⟩, rfl⟩
  · exfalso
    have hne : (E ℓ ω).2 ≠ ⊤ := by rw [← heq]; exact ENNReal.coe_ne_top
    have hs' : (E ℓ ω).2.toNNReal = s := by rw [← heq, ENNReal.toNNReal_coe]
    have h1 := hend hne
    rw [hs'] at h1
    have : (0 : ℝ) < (f (α s)).im := hzH
    rw [h1] at this
    simp at this

end Stage

end InteractingSLE.Theorem14.SB.Qx
