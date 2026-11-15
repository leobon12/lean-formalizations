/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FlStep
import InteractingSLE.Spec.Supplement.SB2QuHead

/-!
# Bookkeeping for the step `ℓ → ℓ + 2`: the line σ-algebras, the zero-time piece, word bounds

Worker PROVE-SB2-F3LAW (target 1).

* **σ-algebras.** For B's program `w` with flow instructions at `ℓ` and `ℓ + 2`: the capped past at the start of `ℓ`
  (`capSpec w ℓ θ 0` through `ℓ + 1`) lies in the past through `ℓ + 1` (`pastSigma w (ℓ + 2)`) and in the capped past
  at the start of `ℓ + 2` (`capSpec w (ℓ + 2) θ 0` through `ℓ + 3`); so does `pastSigma w (ℓ + 1)`
  (`capPast_le_past`, `capPast_le_capPast`, `past_le_capPast`).
* **The piece of a launching stage run for time `0` adds no point of `ℍ`** (GW1's chain facts give the chart's real
  boundary limit at the seed): `stageSet_capSpec_zero_succ`.
* **Word bounds**: `abs_fn_shiftW_le`, `abs_fn_stepWord_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fl

open Restart Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P Lk WalkSide

section Marks

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {w : ExplSpec} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
  {ℓ : ℕ} {θ : ℝ}

theorem capPast_le_past (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤))) :
    pastSigma κ b jumps (capSpec w ℓ θ ((0 : ℝ≥0) : ℝ≥0∞)) E (ℓ + 1) ≤ pastSigma κ b jumps w E (ℓ + 2) := by
  have hℓ : ℓ < w.2.2.length := (List.getElem?_eq_some_iff.1 hwℓ).1
  have h1 := pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps) E hℓ.le hwℓ (0 : ℚ≥0)
  rw [NNRat.cast_zero] at h1
  exact h1.trans (pastSigma_mono w E (Nat.le_succ _))

theorem past_le_capPast {θ' : ℝ} (hℓ₂ : ℓ + 2 ≤ w.2.2.length) {j : ℕ} (hj : j ≤ ℓ + 2) :
    pastSigma κ b jumps w E j ≤
      pastSigma κ b jumps (capSpec w (ℓ + 2) θ' ((0 : ℝ≥0) : ℝ≥0∞)) E (ℓ + 3) := by
  rw [← pastSigma_capSpec_of_le (κ := κ) (b := b) (jumps := jumps) (θ := θ') (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ₂ E hj]
  exact pastSigma_mono _ E (by omega)

theorem capPast_le_capPast {θ' : ℝ} (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (hℓ₂ : ℓ + 2 ≤ w.2.2.length) :
    pastSigma κ b jumps (capSpec w ℓ θ ((0 : ℝ≥0) : ℝ≥0∞)) E (ℓ + 1) ≤
      pastSigma κ b jumps (capSpec w (ℓ + 2) θ' ((0 : ℝ≥0) : ℝ≥0∞)) E (ℓ + 3) :=
  (capPast_le_past E hwℓ).trans (past_le_capPast E hℓ₂ le_rfl)

end Marks

/-- **The piece of a launching stage run for time `0` adds no point of `ℍ`**: under GW1's chain facts, at a launch at
`n` with a driver starting at `0`, the stage set of the capped program `capSpec w n θ 0` through `n + 1` is the stage
set before `n`. -/
theorem stageSet_capSpec_zero_succ {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {θ : ℝ}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω} (hW : WalkChainFacts κ b jumps θ (fun j => E j ω)) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (n + 1)).2.2.2.1 n ≠ none)
    (hE0 : (E n ω).1 0 = 0) :
    WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) n θ ((0 : ℝ≥0) : ℝ≥0∞)) E (n + 1) ω =
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) n θ ((0 : ℝ≥0) : ℝ≥0∞)) E n ω := by
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hlen := lt_length_of_launch _ _ hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  obtain ⟨-, hqP⟩ := prefix_facts hW.1 hW.2 n
  obtain ⟨f, α, C, hf, -, -, -, -, hα, -, -, hs, -, -⟩ := hW.1 n c θ' hcθ (hqP hnd)
  have hc := (eq_launch_of_launches _ _ hcθ).2.2
  rw [WalkLaw.stageSet_succ]
  refine union_eq_left.2 fun z hz => ?_
  exfalso
  unfold WalkLaw.pieceSet at hz
  split_ifs at hz with hlz
  · exact notMem_empty z hz
  rw [WalkSide.run_capSpec_of_le hlen.le _ le_rfl, WalkSide.instrTime_capSpec hlen.le, ENNReal.coe_zero,
    min_eq_left zero_le, ← hc] at hz
  have hα0 : α 0 = 0 := hα.1
  have hf0 : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (f 0)) := hf 0 (by show (0 : ℝ) ≤ (0 : ℂ).im; simp)
  have hq : f 0 = ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) n) : ℝ) : ℂ) := by
    rw [← hα0]
    exact hs
  have := Qu.tipSet_zero_inter_H_eq_empty hf0 hq hE0
  rw [this] at hz
  exact notMem_empty z hz

/-! ### Word bounds -/

theorem abs_fn_shiftW_le {c : BoundaryWord} {M : ℝ} (hc : ∀ y ∉ c.jumps, |c.fn y| ≤ M) (a : ℝ) :
    ∀ y ∉ (BoundaryWord.shiftW a c).jumps, |(BoundaryWord.shiftW a c).fn y| ≤ M := by
  intro y hy
  rw [BoundaryWord.fn_shiftW]
  refine hc _ fun hmem => hy ?_
  rw [BoundaryWord.jumps_shiftW]
  exact Finset.mem_image.2 ⟨y + a, hmem, by ring⟩

theorem abs_fn_stepWord_le {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) {Ω : Type*} (x₀ : Ω → ℝ) {β : Ω → BoundaryWord}
    (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {M : ℝ} (hβ : ∀ ω, ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M) (ω : Ω) :
    ∀ y ∉ (Qw.stepWord κ θ x₀ β e ω).jumps,
      |(Qw.stepWord κ θ x₀ β e ω).fn y| ≤ max M (sleLambda κ + |θ * chiC κ|) :=
  abs_fn_shiftW_le (fun _ hy => Lv.abs_stopWord_fn_le hκ (hβ ω) θ _ hy) _

end InteractingSLE.Theorem14.SB.Fl
