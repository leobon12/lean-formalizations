/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvWalk

/-!
# SB2(2)'s v6 measurability: the rule only sees the runs and the launched traces

Packet PROVE-GW2-GEOM2, round 10 (D28, item (A)). The actual family of the SB2(2) setting is not regular at every
sample, so the v6 rule is read through a regularized family with the same runs. This file shows (deterministically)
that the rule's ingredients agree for two actual families `D₁, Dh` that **agree** (`AgreeAt`):
* the same runs;
* the same lifetimes;
* the same traces at the launched instructions.

* `trOf_congr`, `pcPt_congr`: the chosen trace only sees the driver before its lifetime;
* `entryStage_congr`, `startOff_congr`, `markEntry_congr`, `zeroRoot_congr`, `relOff_congr`: run-only bookkeeping;
* `AgreeAt`, and at an agreeing sample: `launch_iff_of_agree`, `stP_eq_of_agree`, `stL_eq_of_agree`
  (at a launched stage), `mem_cZ4_iff_of_agree` (given the launch at `relOff` off a zero root),
  `cρ3_eq_of_agree`, `mem_denseEv_iff_of_agree`, `mem_maskEv_iff_of_agree`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal LuM GW1W GW1Bookkeep

/-! ### Traces -/

/-- `Exists.choose` of equal predicates. -/
theorem choose_congr {α : Sort*} {p q : α → Prop} (hpq : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    hp.choose = hq.choose := by
  subst hpq
  rfl

/-- **The chosen trace only sees the driver before its lifetime.** -/
theorem trOf_congr {e e' : Drv} (h2 : e.2 = e'.2) (h1 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → e.1 t = e'.1 t) :
    trOf e = trOf e' := by
  have key : (fun η : ℝ≥0 → ℂ => IsGeneratingTrace e.1 e.2 η ∧ (e.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) =
      fun η => IsGeneratingTrace e'.1 e'.2 η ∧ (e'.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
    funext η
    rw [← h2]
    refine propext (and_congr_left' ⟨fun h => ?_, fun h => ?_⟩)
    · exact Sec5.CrossRestart.isGeneratingTrace_congr_drive h fun t ht => (h1 t ht).symm
    · exact Sec5.CrossRestart.isGeneratingTrace_congr_drive h h1
  unfold trOf
  split_ifs with h₁ h₂ h₂
  · exact choose_congr key h₁ h₂
  · exact absurd (key ▸ h₁) h₂
  · exact absurd (key ▸ h₂) h₁
  · rfl

/-- The piece points only see the chosen trace. -/
theorem pcPt_congr (s : ExplState) {e e' : Drv} (h : trOf e = trOf e') : pcPt s e = pcPt s e' := by
  funext t
  unfold pcPt
  rw [h]

/-! ### Run-only bookkeeping -/

section Book

variable {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {R : ℝ} {D D' : ℕ → Drv}

theorem entryStage_congr
    (h : ∀ n, ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D n =
      ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D' n) :
    entryStage κ θ b₁ J₁ R D = entryStage κ θ b₁ J₁ R D' := by
  have key : ∀ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D (n + 1)) ↔
      (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D' (n + 1)) := fun n => by
    rw [h]
  classical
  unfold entryStage
  split_ifs with h₁ h₂ h₂
  · exact le_antisymm (Nat.find_min' h₁ ((key _).2 (Nat.find_spec h₂)))
      (Nat.find_min' h₂ ((key _).1 (Nat.find_spec h₁)))
  · exact absurd (let ⟨n, hn⟩ := h₁; ⟨n, (key n).1 hn⟩) h₂
  · exact absurd (let ⟨n, hn⟩ := h₂; ⟨n, (key n).2 hn⟩) h₁
  · rfl

theorem startOff_congr
    (h : ∀ n, ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D n =
      ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D' n) :
    startOff κ θ b₁ J₁ R D = startOff κ θ b₁ J₁ R D' := by
  unfold startOff
  rw [entryStage_congr h]

theorem markEntry_congr
    (h : ∀ n, ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D n =
      ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D' n) :
    MarkEntry κ θ b₁ J₁ R D ↔ MarkEntry κ θ b₁ J₁ R D' := by
  unfold MarkEntry ArcEntry
  rw [entryStage_congr h, startOff_congr h, h]

theorem zeroRoot_congr
    (h : ∀ n, ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D n =
      ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D' n) :
    ZeroRoot κ θ b₁ J₁ R D ↔ ZeroRoot κ θ b₁ J₁ R D' := by
  unfold ZeroRoot ArcEntry
  rw [entryStage_congr h, markEntry_congr h]

theorem relOff_congr
    (h : ∀ n, ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D n =
      ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D' n) :
    relOff κ θ b₁ J₁ R D = relOff κ θ b₁ J₁ R D' := by
  classical
  unfold relOff
  rw [startOff_congr h]
  by_cases hm : MarkEntry κ θ b₁ J₁ R D
  · simp only [hm, (markEntry_congr h).1 hm, ↓reduceIte]
  · have hm' : ¬ MarkEntry κ θ b₁ J₁ R D' := fun h' => hm ((markEntry_congr h).2 h')
    simp only [hm, hm', ↓reduceIte]

end Book

/-! ### Agreeing actual families -/

section Agree

/-- **Two actual walks agree**: the same runs, the same lifetimes, the same traces at the launched instructions. -/
def AgreeAt (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (D D' : ℕ → Drv) : Prop :=
  (∀ n, ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D n =
      ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D' n) ∧
    (∀ n, (D n).2 = (D' n).2) ∧
    ∀ n, (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D (n + 1)).2.2.2.1 n ≠ none → trOf (D n) = trOf (D' n)

variable {Ω : Type*} {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart}
  {m : ℝ} {D₁ Dh : Ω → ℕ → Drv} {ω : Ω}

theorem relOff_eq_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω)) :
    relOff κ θ b₁ J₁ R (D₁ ω) = relOff κ θ b₁ J₁ R (Dh ω) :=
  relOff_congr h.1

theorem launch_iff_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω)) (j : ℕ) :
    ω ∈ launchEv κ θ b₁ J₁ R D₁ j ↔ ω ∈ launchEv κ θ b₁ J₁ R Dh j := by
  simp only [launchEv, mem_ofPred_eq, wRun]
  rw [relOff_eq_of_agree h, h.1]

theorem stageShift_eq_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω)) {j : ℕ}
    (hl : j = 0 → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
      (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none) :
    stageShift κ θ b₁ J₁ R D₁ j ω = stageShift κ θ b₁ J₁ R Dh j ω := by
  unfold stageShift
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte]
    have htr := h.2.2 _ (hl hj)
    rw [relOff_eq_of_agree h] at htr ⊢
    unfold visitTime
    rw [h.1, h.2.1, pcPt_congr _ htr]
  · simp only [hj, ↓reduceIte]

theorem stL_eq_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω)) {j : ℕ}
    (hl : j = 0 → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
      (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none) :
    stL κ θ b₁ J₁ R D₁ j ω = stL κ θ b₁ J₁ R Dh j ω := by
  unfold stL
  rw [stageShift_eq_of_agree h hl, relOff_eq_of_agree h, h.2.1]

theorem stP_eq_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω)) {j : ℕ} (hj : ω ∈ launchEv κ θ b₁ J₁ R D₁ j)
    (hl : j = 0 → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
      (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none) :
    stP κ θ b₁ J₁ R D₁ j ω = stP κ θ b₁ J₁ R Dh j ω := by
  have hs := stageShift_eq_of_agree (R := R) h hl
  have htr := h.2.2 _ hj
  unfold stP
  simp only [wRun]
  rw [hs]
  rw [relOff_eq_of_agree h] at htr ⊢
  rw [h.1, pcPt_congr _ htr]

/-- Membership in the v4 zero events at an agreeing sample (given the launch at `relOff` off a zero root). -/
theorem mem_cZ4_iff_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω))
    (hl : ¬ ZeroRoot κ θ b₁ J₁ R (D₁ ω) → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
      (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none) (j : ℕ) (F F' : ℕ → Ω → Drv) :
    ω ∈ cZ4 κ θ b₁ J₁ R D₁ j F ↔ ω ∈ cZ4 κ θ b₁ J₁ R Dh j F' := by
  simp only [cZ4, mem_ofPred_eq]
  by_cases hz : ZeroRoot κ θ b₁ J₁ R (D₁ ω)
  · by_cases hj : j = 0
    · have hz' := (zeroRoot_congr (R := R) h.1).1 hz
      simp only [hj, hz, hz', and_self, true_or, or_true]
    · have hL := stL_eq_of_agree (R := R) h (j := j) (fun hj' => absurd hj' hj)
      unfold stL at hL
      rw [hL, zeroRoot_congr h.1]
  · have hL := stL_eq_of_agree (R := R) h (j := j) (fun _ => hl hz)
    unfold stL at hL
    rw [hL, zeroRoot_congr h.1]

/-- The v3 curves at an agreeing sample and a launched stage. -/
theorem cρ3_eq_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω)) {j : ℕ} (hj : ω ∈ launchEv κ θ b₁ J₁ R D₁ j)
    (hl : j = 0 → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
      (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none) (F : ℕ → Ω → Drv) :
    cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F ω = cρ3 κ θ b₁ J₁ b₂ J₂ R c m Dh j F ω := by
  have hP := stP_eq_of_agree (R := R) h hj hl
  have hL := stL_eq_of_agree (R := R) h hl
  unfold stP at hP
  unfold stL at hL
  unfold cρ3 cΦ3
  rw [hP, hL]

theorem mem_denseEv_iff_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω)) {j : ℕ}
    (hj : ω ∈ launchEv κ θ b₁ J₁ R D₁ j)
    (hl : j = 0 → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
      (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none) (F : ℕ → Ω → Drv) :
    ω ∈ denseEv κ θ b₁ J₁ b₂ J₂ R c m D₁ j F ↔ ω ∈ denseEv κ θ b₁ J₁ b₂ J₂ R c m Dh j F := by
  simp only [denseEv, mem_ofPred_eq]
  rw [stP_eq_of_agree h hj hl, stL_eq_of_agree h hl]

/-- **The v6 mask at an agreeing sample** (given the launch at `relOff` off a zero root). -/
theorem mem_maskEv_iff_of_agree (h : AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh ω))
    (hl : ¬ ZeroRoot κ θ b₁ J₁ R (D₁ ω) → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
      (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none) (Gd : Set Ω) (j : ℕ) (F : ℕ → Ω → Drv) :
    ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F ↔ ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m Dh Gd j F := by
  simp only [maskEv, mem_inter_iff, mem_compl_iff]
  rw [mem_cZ4_iff_of_agree h hl j F F]
  constructor
  · rintro ⟨hG, hZ, hL, hR, hD⟩
    have hl0 : j = 0 → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
        (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none := fun hj0 => by
      have := hL; subst hj0; simpa [launchEv] using this
    exact ⟨hG, hZ, (launch_iff_of_agree h j).1 hL, hR, (mem_denseEv_iff_of_agree h hL hl0 F).1 hD⟩
  · rintro ⟨hG, hZ, hL, hR, hD⟩
    have hL' := (launch_iff_of_agree h j).2 hL
    have hl0 : j = 0 → (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1
        (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none := fun hj0 => by
      have := hL'; subst hj0; simpa [launchEv] using this
    exact ⟨hG, hZ, hL', hR, (mem_denseEv_iff_of_agree h hL' hl0 F).2 hD⟩

end Agree

end InteractingSLE.Theorem14.SB.Nv
