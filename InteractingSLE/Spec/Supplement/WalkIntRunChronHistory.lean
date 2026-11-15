/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronCap

/-!
# The actual capped-history input is proved

The cap's effective lifetime is finite even if the original piece has an
infinite lifetime. Append that finite physical arc to its actual old run
history, and reuse the exact capped-carrier raw/range identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep Exist Exist.Staged Exist.StagedLaw WalkBdry WalkIntFill WalkIntChrono

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool}
  {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

variable
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hC : WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)

include hP hC

/-- Every finite cap at an actual launched boundary instruction has a
chronological physical history. This discharges the former hCaps input. -/
theorem arcHistory_capped_launch {α : ℝ≥0 → ℂ} (hα0 : α 0 = 0)
    (τ : ℝ≥0) {k : ℕ} (hk : k < (boundaryWalkSpec b jumps θ right).2.2.length)
    {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (k + 1)).2.2.2.1 k = some (c, θ')) :
    ∃ q : ℂ, ArcHistory (α 0)
      (SB.prefixPhysSet κ b jumps
        (WalkSide.capSpec (boundaryWalkSpec b jumps θ right) k θ τ) D (k + 1)) q := by
  let spec := boundaryWalkSpec b jumps θ right
  have hh := arcHistory_at_launch hP hC hl
  have hp := hP k c θ' hl hh.endpoint_mem
  have hins := (eq_launch_of_launches spec D hl).1
  obtain ⟨hθ, ht⟩ := WalkLeaf.boundaryWalkSpec_inl hins
  have hins' : spec.2.2[k]? = some (Sum.inl (θ, ⊤)) := by
    simpa only [hθ, ht] using hins
  rw [ht, min_top_left] at hp
  let T : ℝ≥0 := (min (τ : ℝ≥0∞) (D k).2).toNNReal
  have hfin : min (τ : ℝ≥0∞) (D k).2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hT : (T : ℝ≥0∞) = min (τ : ℝ≥0∞) (D k).2 := ENNReal.coe_toNNReal hfin
  have hTS : (T : ℝ≥0∞) ≤ (D k).2 := by rw [hT]; exact min_le_right _ _
  obtain ⟨q, hq⟩ := arcHistory_append_finite_tipSet hh hp hTS
  rw [hα0, prefixPhysSet_cap_eq D hk.le hins' hl τ, ← hT]
  exact ⟨q, hq⟩

/-- Every actual live recorded prefix has a chronological history.
The old hCaps premise is proved above, not supplied by the caller. -/
theorem exists_prefixHistory_of_run {α : ℝ≥0 → ℂ} (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hD : ∀ k, IsRegularDriver (D k))
    (R : WalkPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length)) : Nonempty (PrefixHistory R α) := by
  apply exists_prefixHistory_of_capped_histories θ right D hD R hRange
  intro k hk c θ' hl
  exact arcHistory_capped_launch hP hC hα0 R.time hk hl

/-- In the given full proper parameter, every actual raw live prefix is
exactly a seeded initial segment intersected with H. No chronology input. -/
theorem exists_raw_initial_segment_of_run {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hD : ∀ k, IsRegularDriver (D k))
    (R : WalkPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length)) :
    ∃ a : ℝ≥0, R.raw = (α '' Icc 0 a) ∩ QuantumZipper.H := by
  obtain ⟨P⟩ := exists_prefixHistory_of_run hP hC hα0 hRange hD R
  obtain ⟨a, _, ha⟩ := P.exists_initial_segment hα
  exact ⟨a, ha⟩

end InteractingSLE.Theorem14.WalkIntRunChron
