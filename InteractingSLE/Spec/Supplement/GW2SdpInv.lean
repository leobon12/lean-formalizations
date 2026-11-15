/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdpHeight
import InteractingSLE.Spec.Supplement.GW2RootH10Heights

/-!
# The near structure (N3), step A′: the side invariant of the stage words

Packet PROVE-GW2-SDE (round 15). A stage word has, around its tip `0`, the sides of the history pieces and, beyond two
junctions `aL ≤ 0 ≤ aR`, heights carried from the root word:

* `SideInv κ c aL aR HL HR`: on `(aL, 0)` old-left heights, on `(0, aR)` old-right heights, left of `aL` heights in
  `HL`, right of `aR` heights in `HR` (off the jumps);
* **`SideInv.stopWord`**: a stopped piece of an angle in `[−π/2, π/2]` keeps it, with the junctions moved to their
  images `markPosL aL`, `markPos aR` (`GW2Sdp.fn_stopWord_left/right`);
* `junctionL`, `junctionR`: the iterated images of the root along a past; **`sideInv_stageWord`**: every stage word
  `GW2JDetR5.stageWord W₀ θ n x` with angles in `[−π/2, π/2]` has the invariant with these junctions and the root
  word's own left and right heights (`rootHeightsL W₀`, `rootHeightsR W₀`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe v

namespace InteractingSLE.Theorem14.GW2Sdp

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSideHeightProb GW2TipSystem.RootH10

/-- **The side invariant of a word** around its tip, with junctions `aL ≤ 0 ≤ aR`. -/
structure SideInv (κ : ℝ) (c : BoundaryWord) (aL aR : ℝ) (HL HR : Set ℝ) : Prop where
  aL_nonpos : aL ≤ 0
  aR_nonneg : 0 ≤ aR
  oldL : ∀ z, aL < z → z < 0 → z ∉ c.jumps → c.fn z ∈ oldLeftHeights κ
  rootL : ∀ z, z < aL → z ∉ c.jumps → c.fn z ∈ HL
  oldR : ∀ z, 0 < z → z < aR → z ∉ c.jumps → c.fn z ∈ oldRightHeights κ
  rootR : ∀ z, aR < z → z ∉ c.jumps → c.fn z ∈ HR

/-- **A stopped piece keeps the side invariant**, with the junctions moved to their images. -/
theorem SideInv.stopWord {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} {aL aR : ℝ} {HL HR : Set ℝ}
    (h : SideInv κ c aL aR HL HR) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (r : RecData) :
    SideInv κ (stopWord κ (c, θ, r)) (markPosL (rdrv r) (rtime r) aL) (markPos (rdrv r) (rtime r) aR) HL HR where
  aL_nonpos := markPosL_nonpos (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) h.aL_nonpos
  aR_nonneg := markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) h.aR_nonneg
  oldL z hz1 hz2 hzJ := by
    rcases (fn_stopWord_left hκ c θ r h.aL_nonpos hz2 hzJ).1 hz1 with hs | ⟨y, hy1, hy2, hyJ, hy⟩
    · rw [hs]
      exact ⟨θ, hθ, rfl⟩
    · rw [hy]
      exact h.oldL y hy1 hy2 hyJ
  rootL z hz hzJ := by
    have hz0 : z < 0 := hz.trans_le (markPosL_nonpos (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
      h.aL_nonpos)
    obtain ⟨y, hy1, hyJ, hy⟩ := (fn_stopWord_left hκ c θ r h.aL_nonpos hz0 hzJ).2 hz
    rw [hy]
    exact h.rootL y hy1 hyJ
  oldR z hz1 hz2 hzJ := by
    rcases (fn_stopWord_right hκ c θ r h.aR_nonneg hz1 hzJ).1 hz2 with hs | ⟨y, hy1, hy2, hyJ, hy⟩
    · rw [hs]
      exact ⟨θ, hθ, rfl⟩
    · rw [hy]
      exact h.oldR y hy1 hy2 hyJ
  rootR z hz hzJ := by
    have hz0 : 0 < z := (markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) h.aR_nonneg).trans_lt hz
    obtain ⟨y, hy1, hyJ, hy⟩ := (fn_stopWord_right hκ c θ r h.aR_nonneg hz0 hzJ).2 hz
    rw [hy]
    exact h.rootR y hy1 hyJ

/-- The root word's heights left of its root (off the jumps). -/
def rootHeightsL (c : BoundaryWord) : Set ℝ := {h | ∃ y, y < 0 ∧ y ∉ c.jumps ∧ c.fn y = h}

/-- The root word's heights right of its root (off the jumps). -/
def rootHeightsR (c : BoundaryWord) : Set ℝ := {h | ∃ y, 0 < y ∧ y ∉ c.jumps ∧ c.fn y = h}

/-- **The root word has the side invariant with both junctions at the root.** -/
theorem sideInv_root (κ : ℝ) (c : BoundaryWord) : SideInv κ c 0 0 (rootHeightsL c) (rootHeightsR c) where
  aL_nonpos := le_rfl
  aR_nonneg := le_rfl
  oldL _ h1 h2 _ := absurd (h1.trans h2) (lt_irrefl _)
  rootL z hz hzJ := ⟨z, hz, hzJ, rfl⟩
  oldR _ h1 h2 _ := absurd (h1.trans h2) (lt_irrefl _)
  rootR z hz hzJ := ⟨z, hz, hzJ, rfl⟩

section Stage

variable {S : Type v}

/-- **The left junction along a past**: the root `0`, carried by the records' left mark flows. -/
def junctionL : (n : ℕ) → GW2JDetR5.Past S n → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => markPosL (rdrv x.2) (rtime x.2) (junctionL n x.1)

/-- **The right junction along a past.** -/
def junctionR : (n : ℕ) → GW2JDetR5.Past S n → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => markPos (rdrv x.2) (rtime x.2) (junctionR n x.1)

/-- **Every stage word has the side invariant** with the junctions carried along the past and the root word's own
side heights (angles in `[−π/2, π/2]`). -/
theorem sideInv_stageWord {κ : ℝ} (hκ : 0 < κ) (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∀ (n : ℕ) (x : GW2JDetR5.Past S n),
      SideInv κ (GW2JDetR5.stageWord (κ := κ) W₀ θ n x) (junctionL n x) (junctionR n x)
        (rootHeightsL (W₀ (GW2Wm.pastRoot n x))) (rootHeightsR (W₀ (GW2Wm.pastRoot n x)))
  | 0, x => sideInv_root κ (W₀ x)
  | n + 1, x => (sideInv_stageWord hκ W₀ θ hθ n x.1).stopWord hκ (hθ n) x.2

end Stage

end InteractingSLE.Theorem14.GW2Sdp
