/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvHint
import InteractingSLE.Spec.Supplement.GW1ActiveStage

/-!
# Stage words that are sorted and uniformly bounded at every sample

Worker REVIEW-FABLE-T14 (the uniform bound on F3's word; orchestrator split of PROVE-SB2-LCMEAN's handoff R13.8).

SB2(2)'s kernel half needs the retained word sorted and bounded by one constant at **every** sample
(`Mv.SB2LowerBaseLawStatement`, `Mu.integrableOn_chartPairing_of_law`). The landed bound
(`Lv.exists_stageWitness_bounded`) holds almost surely on the launch event only. Here a measurable normalization
of words makes both properties hold everywhere without changing the conditional law:

* `clampW M c`: the heights of `c` clamped to `[−M, M]` (same positions, so same jumps and same sortedness);
  `fn_clampW_of_abs_le`: a height already in `[−M, M]` is unchanged;
* `zeroW` (the zero word) and `normW M c` (`clampW M c` for a sorted `c`, `zeroW` otherwise), measurable, sorted and
  bounded by `M` at every word;
* `isGFFWithBoundaryData_normW`: a law with a sorted word bounded by `M` off its jumps is the law with `normW M`;
* **`exists_stageWitness_sorted_bounded`**: every stage of a staged history with everywhere regular drivers has a
  witness of its conditional law whose word is sorted and bounded by one constant at every sample (the explicit
  stop-word witness `GW1W.isStageWitness_succ_expl` over the bounded witnesses of the earlier stages, normalized).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qt

open Restart Exist Exist.Staged Exist.StagedLaw

/-! ### Clamped and normalized words -/

/-- The heights of a word clamped to `[−M, M]`. -/
def clampW (M : ℝ) (c : BoundaryWord) : BoundaryWord := (c.1, c.2.1, fun i => max (-M) (min M (c.2.2 i)))

theorem fn_clampW (M : ℝ) (c : BoundaryWord) (y : ℝ) : (clampW M c).fn y = max (-M) (min M (c.fn y)) := rfl

theorem jumps_clampW (M : ℝ) (c : BoundaryWord) : (clampW M c).jumps = c.jumps := rfl

theorem isSorted_clampW {M : ℝ} {c : BoundaryWord} (hc : c.IsSorted) : (clampW M c).IsSorted := hc

theorem abs_fn_clampW_le {M : ℝ} (hM : 0 ≤ M) (c : BoundaryWord) (y : ℝ) : |(clampW M c).fn y| ≤ M := by
  rw [fn_clampW]
  exact abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem fn_clampW_of_abs_le {M : ℝ} {c : BoundaryWord} {y : ℝ} (h : |c.fn y| ≤ M) :
    (clampW M c).fn y = c.fn y := by
  obtain ⟨h1, h2⟩ := abs_le.1 h
  rw [fn_clampW, min_eq_right h2, max_eq_right h1]

theorem measurable_clampW (M : ℝ) : Measurable (clampW M) := by
  refine measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk ?_)
  refine measurable_pi_iff.2 fun i => ?_
  have hc : Continuous fun x : ℝ => max (-M) (min M x) := continuous_const.max (continuous_const.min continuous_id)
  exact hc.measurable.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))

/-- The zero word: no jumps, height `0`. -/
def zeroW : BoundaryWord := (0, fun _ => 0, fun _ => 0)

theorem isSorted_zeroW : zeroW.IsSorted := fun _ _ _ hj => absurd hj (Nat.not_lt_zero _)

theorem fn_zeroW (y : ℝ) : zeroW.fn y = 0 := rfl

open Classical in
/-- **The normalized word**: the clamped word when sorted, the zero word otherwise. -/
def normW (M : ℝ) (c : BoundaryWord) : BoundaryWord := if c.IsSorted then clampW M c else zeroW

theorem measurable_normW (M : ℝ) : Measurable (normW M) := by
  classical
  exact Measurable.ite BoundaryWord.measurableSet_isSorted (measurable_clampW M) measurable_const

theorem isSorted_normW (M : ℝ) (c : BoundaryWord) : (normW M c).IsSorted := by
  unfold normW
  split_ifs with hc
  · exact isSorted_clampW hc
  · exact isSorted_zeroW

theorem abs_fn_normW_le {M : ℝ} (hM : 0 ≤ M) (c : BoundaryWord) (y : ℝ) : |(normW M c).fn y| ≤ M := by
  unfold normW
  split_ifs
  · exact abs_fn_clampW_le hM c y
  · rw [fn_zeroW, abs_zero]
    exact hM

theorem normW_of_isSorted {M : ℝ} {c : BoundaryWord} (hc : c.IsSorted) : normW M c = clampW M c := by
  simp only [normW, hc, ↓reduceIte]

/-- **The law does not see the normalization**: a GFF with the data of a sorted word bounded by `M` off its jumps has
the data of the normalized word. -/
theorem isGFFWithBoundaryData_normW {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → DistOn upperHalfPlaneOpens} {M : ℝ} {c : BoundaryWord} (hc : c.IsSorted)
    (hb : ∀ y ∉ c.jumps, |c.fn y| ≤ M) (hY : IsGFFWithBoundaryData Q Y c.fn c.jumps) :
    IsGFFWithBoundaryData Q Y (normW M c).fn (normW M c).jumps := by
  rw [normW_of_isSorted hc, jumps_clampW]
  exact (Restart.isGFFWithBoundaryData_congr Q Y fun y hy => fn_clampW_of_abs_le (hb y hy)).2 hY

/-! ### Sorted, uniformly bounded stage witnesses -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- A stage witness whose word is, almost surely on the launch event, sorted and bounded by one constant. -/
theorem exists_stageWitness_sorted_bounded_ae (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ),
      IsStageWitness κ b jumps P h spec E k β Y ∧ 0 ≤ M ∧
        ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
          (β ω).IsSorted ∧ ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M := by
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨c₀, hc₀, hc₀J, hcb⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
    have hc : c₀.IsSorted := fun i j hij hj => hc₀.monotoneOn (lt_of_le_of_lt hij hj) hj hij
    refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀, fun ω => Exist.flowField spec.1 0 (h ω),
      ∑ i ∈ Finset.range (c₀.1 + 1), |c₀.2.2 i|, GW1W.isStageWitness_zero hh hc₀J hcb,
      Finset.sum_nonneg fun i _ => abs_nonneg _, Eventually.of_forall fun _ _ => ⟨?_, ?_⟩⟩
    · exact BoundaryWord.isSorted_shiftW hc _
    · exact Lv.abs_shiftW_fn_le (fun x _ => Lv.abs_fn_le_sum c₀ x) spec.1
  have Hprev := fun ℓ => Lv.exists_stageWitness_bounded hκ hb hh hE hreg ℓ
  choose β Y M hprev using Hprev
  obtain ⟨βk, Yk, hWk, hexpl⟩ := GW1W.isStageWitness_succ_expl
    (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh hk
    (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j)
    β Y (fun ℓ _ => (hprev ℓ).1)
  set Mk : ℝ := ∑ ℓ ∈ Finset.range k, (M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|)) with hMk
  have hterm : ∀ ℓ ∈ Finset.range k, 0 ≤ M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|) :=
    fun ℓ _ => add_nonneg (hprev ℓ).2.1 (add_nonneg hl.le (abs_nonneg _))
  have hle : ∀ ℓ < k, max (M ℓ) (sleLambda κ + |instrAngle spec ℓ * chiC κ|) ≤ Mk := by
    intro ℓ hℓ
    refine (max_le_add_of_nonneg (hprev ℓ).2.1 (add_nonneg hl.le (abs_nonneg _))).trans ?_
    exact Finset.single_le_sum (f := fun ℓ => M ℓ + (sleLambda κ + |instrAngle spec ℓ * chiC κ|))
      hterm (Finset.mem_range.2 hℓ)
  refine ⟨βk, Yk, Mk, hWk, Finset.sum_nonneg hterm, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ ℓ, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      ∀ y ∉ (β ℓ ω).jumps, |(β ℓ ω).fn y| ≤ M ℓ :=
    ae_all_iff.2 fun ℓ => (hprev ℓ).2.2
  filter_upwards [hall] with ω hω hlk
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
  obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
  have hlℓ : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [hl']
    exact Option.some_ne_none _
  rw [hexpl ℓ ω hℓk hlk hlℓ hn]
  refine ⟨BoundaryWord.isSorted_shiftW (isSorted_stopWord κ _) _, fun y hy => ?_⟩
  exact (Lv.abs_shiftW_fn_le (fun x hx => Lv.abs_stopWord_fn_le hκ (hω ℓ hlℓ) _ _ hx) _ y hy).trans (hle ℓ hℓk)

/-- **Every stage has a witness whose word is sorted and bounded by one constant at every sample.** For a staged
history with everywhere regular drivers and a stage `k`: a witness `(β, Y)` of the conditional law of stage `k`
(`IsStageWitness`) and `M ≥ 0` with `β ω` sorted and `|(β ω).fn y| ≤ M` off its jumps, for every sample `ω`. -/
theorem exists_stageWitness_sorted_bounded (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens) (M : ℝ),
      IsStageWitness κ b jumps P h spec E k β Y ∧ 0 ≤ M ∧ (∀ ω, (β ω).IsSorted) ∧
        ∀ ω, ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M := by
  obtain ⟨β, Y, M, hW, hM, hgood⟩ := exists_stageWitness_sorted_bounded_ae hκ hb hh hE hreg k
  refine ⟨fun ω => normW M (β ω), Y, M, ⟨(measurable_normW M).comp hW.1, hW.2.1, hW.2.2.1, ?_⟩, hM,
    fun ω => isSorted_normW M (β ω), fun ω y _ => abs_fn_normW_le hM (β ω) y⟩
  filter_upwards [hW.2.2.2, hgood] with ω₀ hg hgd hl
  obtain ⟨hs, hbd⟩ := hgd hl
  exact isGFFWithBoundaryData_normW hs hbd (hg hl)

end Stage

end InteractingSLE.Theorem14.SB.Qt
