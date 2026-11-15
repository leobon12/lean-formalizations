/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwCorner

/-!
# SB2(2): the start piece's head before its visit to `R` lies in the hull (`StageFactsAS`, D23)

Packet PROVE-SB2-LIFTSET (round 17). `Mn.StageFactsAll` asks, at the relative root, that the start piece's points up
to its visit time `t_R` of `R` lie in `hullK A`. Given that `β₀`'s head `β₀ '' [0, t_L]` lies in `hullK A`
(`sb2LowerHeadHull`):

* **`head_before_visit`**: at a launch of positive lifetime whose new physical part holds `R`, if `R` is in the old part
  only when the launch starts at `R`, every `pcPt r`, `r ≤ t_R`, is a head point (`startPiece_before` before `t_R`,
  `R = β₀ t_L` at `t_R`; the seed `R` when `R` is old);
* `seed_of_not_arc`: at a pure piece entry the side condition holds (`R` old at the entry stage forces the
  entry stage `0` and `R = 0`, the root).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **The start piece's points up to its visit of `R` are head points**, hence in `hullK A`. -/
theorem head_before_visit (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0} {A : Set ℂ}
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) {R : ℝ} (hβL : β₀ tL = R)
    (hRmem : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hseed : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) →
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = R) :
    ∀ r ≤ visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R,
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) r ∈ hullK A := by
  have hRK : (R : ℂ) ∈ hullK A := hK ⟨tL, ⟨zero_le, le_rfl⟩, hβL⟩
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  by_cases hRo : (R : ℂ) ∈ statePhysicalSet 0 s₁
  · intro r hr
    rw [visitTime_eq_zero_of_old hP hW hl hpos hRo] at hr
    rw [nonpos_iff_eq_zero.1 hr, pcPt_zero_launch hP hW hl hpos, hseed hRo]
    exact hRK
  · have hsplit : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) =
        statePhysicalSet 0 s₁ ∪ (newPc s₁ (D n)).1.tipSet (newPc s₁ (D n)).2.1 (newPc s₁ (D n)).2.2 := by
      rw [GW1W.launch_walk hl]
      exact GW1WalkChain.statePhysicalSet_launch 0 _ n (D n) θ ⊤
    rw [hsplit] at hRmem
    have hRt := hRmem.resolve_left hRo
    obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
    rw [htip] at hRt
    obtain ⟨t₀, ht₀, ht₀R⟩ := hRt
    obtain ⟨hshK, hsh, hmin⟩ := visitTime_spec hP hl ⟨t₀, ht₀, ht₀R⟩
    have hbefore := startPiece_before hP hW hl hpos hβ hβ0 hβr (tL := tL) (by rw [hβL]; exact hRo)
      (sh := visitTime s₁ (D n) R) (fun t ht h => hmin t ht (h.trans hβL)) hshK
    intro r hr
    rcases eq_or_lt_of_le hr with heq | hlt
    · rw [heq, hsh]; exact hRK
    · have hrK : (r : ℝ≥0∞) ≤ (D n).2 := le_trans (ENNReal.coe_le_coe.2 hr) hshK
      have hmemR : pcPt s₁ (D n) r ∈ range β₀ := by
        rw [hβr]
        exact tipSet_subset_physSet_launch hl (by rw [htip]; exact ⟨r, hrK, rfl⟩)
      obtain ⟨t', ht'⟩ := hmemR
      have hlt' := hbefore r hlt t' ht'
      rw [← ht']
      exact hK ⟨t', ⟨zero_le, hlt'.le⟩, rfl⟩

/-- **At a pure piece entry the side condition holds**: `R` old at the entry stage forces the entry stage `0` and the
root `R = 0`. -/
theorem seed_of_not_arc {R : ℝ}
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hA : ¬ ArcEntry κ θ b jumps R D) (hM : ¬ MarkEntry κ θ b jumps R D) :
    (R : ℂ) ∈ statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) →
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) = R := by
  intro hR
  have ho : relOff κ θ b jumps R D = entryStage κ θ b jumps R D := by
    rw [relOff_of_not_mark κ θ b jumps hM, (startOff_eq κ θ b jumps R D).2 hA]
  obtain ⟨-, hmin⟩ := entryStage_spec κ θ b jumps hex
  rw [ho] at hR ⊢
  rcases Nat.eq_zero_or_pos (entryStage κ θ b jumps R D) with h0 | hpos
  · rw [h0] at hR ⊢
    have h1 : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = {0} :=
      statePhysicalSet_init
    rw [h1, mem_singleton_iff] at hR
    have : R = 0 := by exact_mod_cast hR
    rw [this]
    rfl
  · exfalso
    have := hmin (entryStage κ θ b jumps R D - 1) (by omega)
    rw [show entryStage κ θ b jumps R D - 1 + 1 = entryStage κ θ b jumps R D by omega] at this
    exact this hR

end InteractingSLE.Theorem14.SB.Lk
