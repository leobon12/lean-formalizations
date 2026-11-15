/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MdFill

/-!
# The lift images of the prefixes (the last walk-side inputs of `fillCorr_of_chain`)

Packet PROVE-T14-SB2LIFT (round 18). `fillCorr_of_chain` asks, at a pair of corresponding launches, that the relative
prefix after the launch be the lift image of the actual one (`hP₂eq`), and the same at matching times of the two pieces
(`hmatch₁`, `hmatch₂`). This file reduces both to per-stage and per-piece data, with no circularity with the lockstep
induction: the stage identity before the launch comes from PROVE-SB2-LIFTSET's history correspondence `AccCorr`, and
the new pieces from their own lift relation.

* `prefixPhysSet_succ_of_launch`: a launch adds exactly its new piece to the prefix;
* **`statePhysicalSet_eq_liftImage_of_accCorr`**: under `AccCorr` with the lift relation as the piece relation, the
  relative physical part is the lift image of the actual one, given the start part and the new connectors
  (`liftImage_ofReal`);
* **`prefix_succ_eq_liftImage_of_launch`**: from the stage identity and the lift relation of the new pieces (the piece
  datum `StepPiece`), the identity after the launch;
* **`partPrefix_eq_liftImage`**: from the stage identity and a lift of the new pieces up to matching times, the identity
  at those times;
* **`fillCorr_of_stage`**: `FillCorr` from these data (`fillCorr_of_chain` with its lift-image inputs discharged).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ι : ℝ → ℝ} {p : ℝ}

/-- **A launch adds exactly its new piece to the prefix.** -/
theorem prefixPhysSet_succ_of_launch {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} {c : Chart}
    {θ' : ℝ} (hl : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1)).2.2.2.1 n = some (c, θ')) :
    SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1) =
      SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D n ∪
        (newPc (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) (D n)).1.tipSet
          (newPc (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) (D n)).2.1
          (newPc (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) (D n)).2.2 := by
  have hlne : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1)).2.2.2.1 n ≠ none := by
    rw [hl]; simp
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := J) _ D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
  have hY := GW1Bookkeep.pieces_run_succ_of_launch hlne
  have hZ : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1)).2.1 =
      (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n).2.1 ++ [] := by
    rw [he, Lx.arcs_launch', List.append_nil]
  have h := statePhysicalSet_append (x := 0) hY hZ
  change statePhysicalSet 0 (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1)) =
    statePhysicalSet 0 (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) ∪ _
  rw [h]
  ext z
  simp only [mem_union, List.mem_singleton, mem_iUnion, exists_prop, exists_eq_left, List.not_mem_nil, false_and,
    exists_false, or_false]
  rfl

/-- **The relative physical part is the lift image of the actual one under the history correspondence.** -/
theorem statePhysicalSet_eq_liftImage_of_accCorr {t₁ t₂ s₁ s₂ : ExplState}
    (hc : AccCorr ι p (LiftRel β₀ tL γ) t₁ t₂ s₁ s₂)
    (hstart : statePhysicalSet 0 t₂ = liftImage β₀ tL γ (statePhysicalSet 0 t₁))
    (harcs : ∀ X : List (Set ℝ), s₁.2.1 = t₁.2.1 ++ X → ∀ a ∈ X,
      liftImage β₀ tL γ (((↑) : ℝ → ℂ) '' a) = ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici p))) :
    statePhysicalSet 0 s₂ = liftImage β₀ tL γ (statePhysicalSet 0 s₁) := by
  obtain ⟨-, ⟨X, hX₁, hX₂⟩, Y₁, Y₂, hY₁, hY₂, hY⟩ := hc
  rw [statePhysicalSet_append hY₂ hX₂, statePhysicalSet_append hY₁ hX₁, liftImage_union, liftImage_union,
    liftImage_biUnion, liftImage_biUnion, hstart, biUnion_eq_of_forall₂ hY]
  congr 1
  simp only [List.mem_map, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]
  exact (iUnion₂_congr fun a ha => harcs X hX₁ a ha).symm

/-- **The identity after a pair of corresponding launches** from the identity before them and the lift relation of the
new pieces. -/
theorem prefix_succ_eq_liftImage_of_launch {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart}
    {θ₁ θ₂ : ℝ}
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hstage : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂ =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hpc : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) (D₁ n₁))
      (newPc (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) (D₂ n₂))) :
    SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)) := by
  rw [prefixPhysSet_succ_of_launch hl₁, prefixPhysSet_succ_of_launch hl₂, liftImage_union, ← hstage]
  exact congrArg _ hpc

/-- **The identity at matching times of the two pieces** from the identity before the launches and a lift of the new
pieces up to those times. -/
theorem partPrefix_eq_liftImage {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ}
    (hstage : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂ =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    {r r' : ℝ}
    (htr : bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ''
        (trOf (D₂ n₂) '' Icc 0 r'.toNNReal) =
      liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ''
        (trOf (D₁ n₁) '' Icc 0 r.toNNReal))) :
    partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r) := by
  unfold partPrefix
  rw [liftImage_union, ← hstage, ← htr]

variable {R : ℝ}

/-- **`FillCorr` from the stage identity before the launches, the lift relation of the new pieces and their lift at
matching times** (`fillCorr_of_chain` with `hP₂eq`, `hmatch₁`, `hmatch₂` discharged). -/
theorem fillCorr_of_stage {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hβ : Supp9B.IsProperCurve β₀) (hD : LiftCurveData β₀ γ tL R ι)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβ0 : β₀ 0 = 0)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, NoLeftMove κ b₁ J₁ θ D₁ k) (hn₁ : n₁ + 1 ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hL : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, NoLeftMove κ b₂ J₂ θ D₂ k)
    (hstage : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂ =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hpc : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) (D₁ n₁))
      (newPc (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) (D₂ n₂)))
    (htr₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ''
          (trOf (D₂ n₂) '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ''
          (trOf (D₁ n₁) '' Icc 0 r.toNNReal)))
    (htr₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ''
          (trOf (D₂ n₂) '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ''
          (trOf (D₁ n₁) '' Icc 0 r.toNNReal))) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι := by
  refine fillCorr_of_chain hι hβ hD hβr hβ0 hRa hrecc hP₁ hW₁ hl₁ hfin₁ hrec₁ hlm₁ hn₁ hL hP₂ hl₂ hfin₂ hrec₂ hlm₂
    (prefix_succ_eq_liftImage_of_launch hl₁ hl₂ hstage hpc) (fun r hr0 hr => ?_) (fun r' hr0' hr' => ?_)
  · obtain ⟨r', hr0', hr', h⟩ := htr₁ r hr0 hr
    exact ⟨r', hr0', hr', partPrefix_eq_liftImage hstage h⟩
  · obtain ⟨r, hr0, hr, h⟩ := htr₂ r' hr0' hr'
    exact ⟨r, hr0, hr, partPrefix_eq_liftImage hstage h⟩

end InteractingSLE.Theorem14.SB.Lk
