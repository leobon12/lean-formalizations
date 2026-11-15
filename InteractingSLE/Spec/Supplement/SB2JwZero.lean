/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwAct

/-!
# SB2(2): the zero-lifetime relative stage `0` (D6 v3, item 2)

Packet PROVE-SB2-LIFTSET (round 17).

* `mem_succ_of_not_zeroRoot`: off a zero root, `R` is in the physical part after the launch at `relOff` (a mark entry
  holds `R` before it; a pure piece entry adds it at `relOff`);
* `tipSet_zero_launch`: a zero-lifetime launched piece is its seed;
* **`stPt_eq_of_zero_life`**: off a zero root, a zero-lifetime piece at `relOff` (positive lifetimes after stage `0`)
  is launched from `R` — `relOff = 0`, and `R` is either the seed or in the initial part `{0}`;
* **`liftRel_zero_stage0`**: then the lift relation with a regular zero-lifetime relative piece from the root holds
  (both tips are single points: `{R}` lifts to `{γ 0} = {0}`).
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

/-- **Off a zero root, `R` is in the physical part after the launch at `relOff`.** -/
theorem mem_succ_of_not_zeroRoot {R : ℝ}
    (hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hZ : ¬ ZeroRoot κ θ b jumps R D) :
    (R : ℂ) ∈ statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D + 1)) := by
  classical
  by_cases hM : MarkEntry κ θ b jumps R D
  · exact statePhysicalSet_mono (Nat.le_succ _) (mem_statePhysicalSet_of_mark hR hM)
  · have hA : ¬ ArcEntry κ θ b jumps R D := fun hA => hZ ⟨hA, hM⟩
    rw [relOff_of_not_mark κ θ b jumps hM, (startOff_eq κ θ b jumps R D).2 hA]
    exact (entryStage_spec κ θ b jumps (exists_mem_statePhysicalSet_succ hR)).1

/-- **A zero-lifetime launched piece is its seed.** -/
theorem tipSet_zero_launch (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (h0 : (D n).2 = 0) :
    (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 =
      {((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ)} := by
  have hcap := tip_inter_old_eq hW hl
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hsing : (newPc s₁ (D n)).1.tipSet (newPc s₁ (D n)).2.1 (newPc s₁ (D n)).2.2 = {pcPt s₁ (D n) 0} := by
    rw [htip]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht0 : (t : ℝ≥0∞) = 0 := nonpos_iff_eq_zero.1 (by rw [← h0]; exact ht)
      rw [ENNReal.coe_eq_zero.1 ht0]
      rfl
    · intro hz
      rw [mem_singleton_iff.1 hz]
      exact ⟨0, by simp, rfl⟩
  rw [hsing] at hcap ⊢
  have hmem : ((stPt s₁ : ℝ) : ℂ) ∈ {pcPt s₁ (D n) 0} ∩ statePhysicalSet 0 s₁ := by
    rw [hcap]; exact mem_singleton _
  rw [mem_singleton_iff.1 hmem.1]

/-- **A zero-lifetime piece at `relOff` is launched from `R`** (off a zero root, with positive lifetimes after stage
`0`). -/
theorem stPt_eq_of_zero_life (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hpos : ∀ n, 0 < n → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none →
      (D n).2 ≠ 0) {R : ℝ}
    (hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hZ : ¬ ZeroRoot κ θ b jumps R D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D + 1)).2.2.2.1
      (relOff κ θ b jumps R D) ≠ none)
    (h0 : (D (relOff κ θ b jumps R D)).2 = 0) :
    ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D)) : ℝ) : ℂ) =
      (R : ℂ) := by
  have hmem := mem_succ_of_not_zeroRoot hR hZ
  have ho : relOff κ θ b jumps R D = 0 := by
    by_contra h
    exact hpos _ (Nat.pos_of_ne_zero h) hl h0
  rw [GW1W.launch_walk hl, GW1WalkChain.statePhysicalSet_launch] at hmem
  have htip := tipSet_zero_launch hP hW hl h0
  rcases hmem with hold | hnew
  · rw [ho] at hold ⊢
    have h1 : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = {0} :=
      statePhysicalSet_init
    rw [h1, mem_singleton_iff] at hold
    rw [hold]
    rfl
  · have hnew' : (R : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
        (relOff κ θ b jumps R D)) (D (relOff κ θ b jumps R D))).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D))
          (D (relOff κ θ b jumps R D))).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D))
          (D (relOff κ θ b jumps R D))).2.2 := hnew
    rw [htip] at hnew'
    exact (mem_singleton_iff.1 hnew').symm

/-- **The lift relation at a zero-lifetime relative stage `0`**: the actual piece is the single point `R = β₀ t_L`, the
relative one the root `0 = γ 0`. -/
theorem liftRel_zero_stage0 (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hpos : ∀ n, 0 < n → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none →
      (D n).2 ≠ 0) {R : ℝ}
    (hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hZ : ¬ ZeroRoot κ θ b jumps R D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D + 1)).2.2.2.1
      (relOff κ θ b jumps R D) ≠ none)
    (h0 : (D (relOff κ θ b jumps R D)).2 = 0) {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} (hβ : IsProperCurve β₀)
    (hβL : β₀ tL = R) (hγ0 : γ 0 = 0) {e₂ : Drv} (hreg : IsRegularDriver e₂) (he₂ : e₂.2 = 0) :
    LiftRel β₀ tL γ
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (relOff κ θ b jumps R D))
        (D (relOff κ θ b jumps R D)))
      (newPc (ExplState.init 0) e₂) := by
  have hseed := stPt_eq_of_zero_life hP hW hpos hR hZ hl h0
  unfold LiftRel liftImage
  rw [tipSet_newPc_init_zero hreg he₂, tipSet_zero_launch hP hW hl h0, hseed]
  ext z
  constructor
  · intro hz
    rw [mem_singleton_iff.1 hz]
    exact ⟨0, show β₀ (tL + 0) ∈ ({(R : ℂ)} : Set ℂ) by rw [add_zero, hβL]; exact mem_singleton _, hγ0⟩
  · rintro ⟨s, hs, rfl⟩
    have hs' : β₀ (tL + s) = β₀ tL := by rw [hβL]; exact hs
    have hs0 : tL + s = tL + 0 := by rw [add_zero]; exact hβ.2.1 hs'
    rw [add_left_cancel hs0, hγ0]
    exact mem_singleton _

end InteractingSLE.Theorem14.SB.Lk
