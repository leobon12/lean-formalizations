/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LvInv

/-!
# The launch observables of the lifted walk from the fill correspondence

Packet PROVE-T14-SB2LIFT (round 11; item 1 of handoff §R10.2). At corresponding launches of the actual lower walk
(data `b₁`, drivers `D₁`, stage `n₁`) and of SB2(2)'s relative walk (data `b₂`, drivers `D₂`, stage `n₂`), the
lockstep step data `StepOK` needs the new records to correspond and the right hits to occur together. Both are
consequences of two inputs:

* the record invariants `RecInv` of both runs (`SB2LvInv`, proved along each run from finite lifetimes and
  `WalkMovesRight`);
* the **fill correspondence** on the right ray beyond the records (`FillCorr`), the remaining geometric fact. A point
  `x` beyond the actual record is in the closure of the new actual filled prefix iff `ι x` is in that of the new
  relative one. Likewise, `x` is in the closure of the filled set of the old prefix and a proper initial part of the
  piece iff `ι x` is, for the relative run. The second form is a union over the earlier times of either piece, so it
  does not depend on the two time parametrizations.

Results:

* **`lRecR_launch_corr`**: the new relative record is the `ι`-image of the new actual one (`lRecR_corr` with
  `lRecR_run_eq` and `lAlive_run_iff`);
* **`lHit_launch_corr`**: right hits beyond the records occur in both runs or in neither (`lHit_run_iff`).

`ι` is a right-ray correspondence (`RayCorr`) that is moreover continuous on `[R, ∞)`, with `recR₂ = ι recR₁` and
`R ≤ recR₁`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}

/-- The physical prefix of a walk run with the piece of stage `n` up to time `r`. -/
def partPrefix (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) (r : ℝ) : Set ℂ :=
  SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D n ∪
    bdVal (stChart (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n)) '' (trOf (D n) '' Icc 0 r.toNNReal)

/-- **Named input: the fill correspondence of the two runs beyond the records** (at one pair of launches). -/
def FillCorr (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (D₁ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n₁ : ℕ) (b₂ : ℝ → ℝ)
    (J₂ : Finset ℝ) (D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n₂ : ℕ) (ι : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) < x →
    ((x : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1))) ↔
      ((ι x : ℝ) : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1))))) ∧
  ∀ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) < x →
    ((∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧ (x : ℂ) ∈ closure (fillH (partPrefix κ b₁ J₁ θ D₁ n₁ r))) ↔
      ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₂ n₂) ∧ ((ι x : ℝ) : ℂ) ∈ closure (fillH (partPrefix κ b₂ J₂ θ D₂ n₂ r)))

/-- Points beyond the record of a launch with a finite lifetime in the closure of the new fill form a bounded set. -/
theorem bddAbove_beyond_fill {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) {n : ℕ} (hfin : (D n).2 ≠ ⊤)
    (hok : RecInv κ b J θ D n) (a : ℝ) :
    BddAbove {x : ℝ | a < x ∧
      (x : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b J (boundaryWalkSpec b J θ true) D (n + 1)))} := by
  have hfin'' : ∀ j < n + 1, (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤ := by
    intro j hj hj'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact recInv_fin hok j hj hj'
    · exact hfin
  obtain ⟨K, hKc, hKR, -⟩ := image_runChart_walk hP (n + 1) hfin''
  have hfill := fillH_eq_of_union_im hKR
  obtain ⟨M, hM⟩ := ((isBounded_fillH hKc.isClosed hKc.isBounded).closure).subset_closedBall 0
  rw [hfill] at hM
  refine ⟨M, fun x hx => ?_⟩
  have h1 := hM hx.2
  rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
  exact (le_abs_self x).trans h1

/-- **The new records correspond.** -/
theorem lRecR_launch_corr {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {R : ℝ} {ι : ℝ → ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hok₁ : RecInv κ b₁ J₁ θ D₁ n₁)
    (hok₂ : RecInv κ b₂ J₂ θ D₂ n₂)
    (hR : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrec : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hF : FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι) :
    lRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ⊤ (D₂ n₂) =
      ι (lRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ⊤ (D₁ n₁)) := by
  refine lRecR_corr hι.mono hcont hR hrec (fun x hx => ?_) (fun y hy => ?_) (fun y hy => ?_) hF.1
    (bddAbove_beyond_fill hP₁ hfin₁ hok₁ _)
  · obtain ⟨h1, h2, h3, h4⟩ := hok₁ x hx
    exact lAlive_run_iff hP₁ hl₁ hfin₁ x h1 h2 h3 h4
  · obtain ⟨h1, h2, h3, h4⟩ := hok₂ y hy
    exact lAlive_run_iff hP₂ hl₂ hfin₂ y h1 h2 h3 h4
  · rw [hrec] at hy
    obtain ⟨x, hxR, rfl⟩ := hι.exists_ge hR hy.le
    refine ⟨x, ?_, rfl⟩
    rcases eq_or_lt_of_le hxR with he | hlt
    · rw [← he] at hy; exact absurd hy (lt_irrefl _)
    · exact hlt

/-- **Right hits beyond the records occur in both runs or in neither.** -/
theorem lHit_launch_corr {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {R : ℝ} {ι : ℝ → ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hok₁ : RecInv κ b₁ J₁ θ D₁ n₁)
    (hok₂ : RecInv κ b₂ J₂ θ D₂ n₂)
    (hR : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrec : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hF : FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι) :
    (∃ x : ℝ, stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) < x ∧
      lHit (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ⊤ (D₂ n₂) x) ↔
    ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) < x ∧
      lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ⊤ (D₁ n₁) x := by
  set r₁ := stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) with hr₁
  set r₂ := stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) with hr₂
  -- the hit of an actual point beyond the record is the hit of its image
  have key : ∀ x : ℝ, r₁ < x →
      (lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ⊤ (D₁ n₁) x ↔
        lHit (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ⊤ (D₂ n₂) (ι x)) := by
    intro x hx
    have hxR : R ≤ x := hR.trans hx.le
    have hy : r₂ < ι x := lt_of_eq_of_lt hrec ((hι.lt_iff hR hxR).2 hx)
    rw [lHit_run_iff hP₁ hl₁ hfin₁ (hok₁ x hx), lHit_run_iff hP₂ hl₂ hfin₂ (hok₂ _ hy)]
    have h1 := hF.1 x hx
    have h2 := hF.2 x hx
    simp only [partPrefix] at h2
    constructor
    · rintro ⟨hA, hB⟩
      refine ⟨fun r hr0 hrT hm => ?_, h1.1 hB⟩
      obtain ⟨r', hr'0, hr'T, hm'⟩ := h2.2 ⟨r, hr0, hrT, hm⟩
      exact hA r' hr'0 hr'T hm'
    · rintro ⟨hA, hB⟩
      refine ⟨fun r hr0 hrT hm => ?_, h1.2 hB⟩
      obtain ⟨r', hr'0, hr'T, hm'⟩ := h2.1 ⟨r, hr0, hrT, hm⟩
      exact hA r' hr'0 hr'T hm'
  constructor
  · rintro ⟨y, hy, hhit⟩
    have hy' : ι r₁ ≤ y := by rw [← hrec]; exact hy.le
    obtain ⟨x, hxr, rfl⟩ := hι.exists_ge hR hy'
    have hx : r₁ < x := by
      rcases eq_or_lt_of_le hxr with he | hlt
      · rw [← he, ← hrec] at hy; exact absurd hy (lt_irrefl _)
      · exact hlt
    exact ⟨x, hx, (key x hx).2 hhit⟩
  · rintro ⟨x, hx, hhit⟩
    have hy : r₂ < ι x := lt_of_eq_of_lt hrec ((hι.lt_iff hR (hR.trans hx.le)).2 hx)
    exact ⟨ι x, hy, (key x hx).1 hhit⟩

end InteractingSLE.Theorem14.SB.Lk
