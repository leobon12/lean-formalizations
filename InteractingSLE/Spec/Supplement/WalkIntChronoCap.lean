/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntChronoRange

/-!
# The capped program gives the physical carrier of a recorded prefix

The raw-set equality is proved by the existing capped-program identity.
The remaining named run input concerns its chronological ArcHistory.
Inclusion in the full proper walk, including real connectors, is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntChrono

open WalkBdry WalkMean WalkIntFill GW1WalkChain Exist.StagedLaw

/-- Every selected recorded live prefix has the capped program's full
physical carrier, whose intersection with H is exactly its raw prefix set. -/
theorem exists_capped_carrier {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    (R : WalkPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length)) :
    ∃ k, k < (boundaryWalkSpec b jumps θ right).2.2.length ∧ ∃ c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') ∧
      (boundaryWalkSpec b jumps θ right).2.2[k]? = some (Sum.inl (θ, ⊤)) ∧
      (R.time : ℝ≥0∞) < (D k).2 ∧
      SB.prefixPhysSet κ b jumps
        (WalkSide.capSpec (boundaryWalkSpec b jumps θ right) k θ R.time) D (k + 1) ∩ H =
          R.raw := by
  let w := boundaryWalkSpec b jumps θ right
  obtain ⟨k, hk, θ', hl, hpre, hpc⟩ := WalkSide.exists_launch_of_pieces_eq
    (κ := κ) (b := b) (jumps := jumps) w D w.2.2.length R.split
  have hins := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) w D hl).1
  obtain ⟨hθ, ht⟩ := WalkLeaf.boundaryWalkSpec_inl hins
  have hins' : w.2.2[k]? = some (Sum.inl (θ, ⊤)) := by
    simpa only [hθ, ht] using hins
  rw [ht] at hpc
  have hτ : (R.time : ℝ≥0∞) < min ⊤ (D k).2 := by
    have h := R.alive
    rwa [hpc] at h
  let E : ℕ → Unit → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j _ => D j
  have hset := WalkSide.prefixSet_eq_stageSet (κ := κ) (b := b) (jumps := jumps)
    E () hk.le hins' hl (hD k) hτ
  have hphys : SB.prefixPhysSet κ b jumps (WalkSide.capSpec w k θ R.time) D (k + 1) ∩ H =
      WalkLaw.stageSet κ b jumps (WalkSide.capSpec w k θ R.time) E (k + 1) () :=
    WalkIntFiber.physOf_inter_H _ _
  refine ⟨k, hk, (ExplState.run κ b jumps w D k).2.2.2.2.1, θ', hl, hins', ?_, ?_⟩
  · simpa only [min_top_left] using hτ
  change _ = prefixSet R.pre R.piece R.time
  rw [hpc, ← hpre]
  exact hphys.trans hset.symm

/-- The exact remaining capped-run history input constructs the physical
prefix certificate. Its raw-set equality has already been proved above. -/
theorem exists_prefixHistory_of_capped_histories {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    (R : WalkPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length)) {α : ℝ≥0 → ℂ}
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hCaps : ∀ k, k < (boundaryWalkSpec b jumps θ right).2.2.length → ∀ c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      ∃ q, ArcHistory (α 0)
          (SB.prefixPhysSet κ b jumps
            (WalkSide.capSpec (boundaryWalkSpec b jumps θ right) k θ R.time) D (k + 1)) q) :
    Nonempty (PrefixHistory R α) := by
  obtain ⟨k, hk, c, θ', hl, hins, hτ, hraw⟩ := exists_capped_carrier θ right D hD R
  obtain ⟨q, hhistory⟩ := hCaps k hk c θ' hl
  refine ⟨⟨_, q, hhistory, hraw, ?_⟩⟩
  rw [hRange]
  exact capped_physical_subset_walk D hk hins hl (hD k) hτ

end InteractingSLE.Theorem14.WalkIntChrono
