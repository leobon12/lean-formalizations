/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3LtCap

/-!
# Lemma S3 for SB2(2)'s lower tail: the cut on a common arc

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 with the roles exchanged, supplement p. 631). Deterministic.

* `exists_rat_cut`: a continuous point map landing at `t₀ > 0` on an open arc of a proper curve lands on that arc at a
  rational earlier time (the arc is relatively open: proper curves are closed embeddings);
* **`exists_walk_cut`**: every open arc of the lower walk in `ℍ` contains a cut `β₀(τ) = ĝ(α(q))` on a launched piece at
  a **rational** own time `q`, with all inputs of `second_sample_facts_walk` (so the second histories form a countable
  family of capped programs).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv chiC)

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart WalkSide Geo Canon GW1Bookkeep
open Supp9B (IsProperCurve)

/-- **A rational earlier time on the same open arc.** A point map continuous on `{t ≤ S}` with values on a proper
curve `β₀`, landing at an interior time `t₀ > 0` on the open arc `β₀((s₁, s₂))`, lands on that arc at some rational
time in `(0, t₀)`. -/
theorem exists_rat_cut {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) {s₁ s₂ : ℝ≥0} {S : ℝ≥0∞} {φ : ℝ≥0 → ℂ}
    (hφ : ContinuousOn φ {t | (t : ℝ≥0∞) ≤ S}) (hφr : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → φ t ∈ range β₀)
    {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) ≤ S) (ht₀0 : 0 < t₀) (hφt₀ : φ t₀ ∈ β₀ '' Ioo s₁ s₂) :
    ∃ q : ℚ, 0 < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal < t₀ ∧ φ (q : ℝ).toNNReal ∈ β₀ '' Ioo s₁ s₂ := by
  have he := (Lk.isClosedEmbedding_of_isProperCurve hβ).isInducing
  obtain ⟨U, hU, hUe⟩ := he.isOpen_iff.1 (isOpen_Ioo (a := s₁) (b := s₂))
  obtain ⟨τ, hτ, hτe⟩ := hφt₀
  have hφU : φ t₀ ∈ U := by
    rw [← hτe]
    show τ ∈ β₀ ⁻¹' U
    rw [hUe]; exact hτ
  have hev : φ ⁻¹' U ∈ 𝓝[{t : ℝ≥0 | (t : ℝ≥0∞) ≤ S}] t₀ := (hφ t₀ ht₀) (hU.mem_nhds hφU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have ht₀r : (0 : ℝ) < (t₀ : ℝ) := by exact_mod_cast ht₀0
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn
    (show max ((t₀ : ℝ) - ε) 0 < (t₀ : ℝ) from max_lt (by linarith) ht₀r)
  have hr0 : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt (le_max_right _ _) hr1
  have hr1' : (t₀ : ℝ) - ε < (r : ℝ) := lt_of_le_of_lt (le_max_left _ _) hr1
  have hq'r : (((r : ℝ).toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0.le
  have hqt : (r : ℝ).toNNReal < t₀ := by
    rw [← NNReal.coe_lt_coe, hq'r]; exact hr2
  refine ⟨r, Real.toNNReal_pos.2 hr0, hqt, ?_⟩
  have hq'S : (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S := (ENNReal.coe_le_coe.2 hqt.le).trans ht₀
  have hmem : (r : ℝ).toNNReal ∈ ball t₀ ε ∩ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} := by
    refine ⟨?_, hq'S⟩
    rw [mem_ball, NNReal.dist_eq, hq'r, abs_sub_lt_iff]
    constructor <;> linarith
  have hU' : φ (r : ℝ).toNNReal ∈ U := hball hmem
  obtain ⟨τ', hτ'⟩ := hφr _ hq'S
  refine ⟨τ', ?_, hτ'⟩
  rw [← hUe]
  show β₀ τ' ∈ U
  rw [hτ']; exact hU'

end InteractingSLE.Theorem14.SB.S3.Asm

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart WalkSide Geo Canon GW1Bookkeep
open Supp9B (IsProperCurve)

/-- **The cut of a common arc of the lower walk in `ℍ`** (deterministic). For the lower walk run with drivers `D`
(GW1's per-step facts, regular launches, injective traces, tip coordinates), done at `N`, and a proper parametrization
`β₀` of its physical set: every open arc `β₀((s₁, s₂)) ⊆ ℍ` contains a cut point `β₀(σ) = ĝ(α(q))` on a launched piece
`j < N` at a **rational** own time `q > 0` below its lifetime, with `α(q) ∈ ℍ`; together with every input of
`second_sample_facts_walk` at `(j, q)`. -/
theorem exists_walk_cut {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hW : Lk.WalkChainFacts κ b jumps (-(Real.pi / 2)) D)
    (hreg : LuM.RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D)
    (hinj : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (j + 1)).2.2.2.1 j ≠
      none → InjOn (LuM.trOf (D j)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2})
    (htip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D)
    {N : ℕ} (hdN : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D N) =
      GW1Conn.stDone)
    {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀)
    (hβr : range β₀ = statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D N))
    {s₁ s₂ : ℝ≥0} (hs : s₁ < s₂) (harc : β₀ '' Ioo s₁ s₂ ⊆ H) :
    ∃ (j : ℕ) (c : Chart) (θ' : ℝ) (q : ℚ) (s₁' Cg : ℝ) (gc : ℂ → ℂ) (τ : ℝ≥0),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (j + 1)).2.2.2.1 j =
        some (c, θ') ∧
      0 < (q : ℝ).toNNReal ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D j).2 ∧ LuM.trOf (D j) (q : ℝ).toNNReal ∈ H ∧
      τ ∈ Ioo s₁ s₂ ∧ β₀ τ = gc (LuM.trOf (D j) (q : ℝ).toNNReal) ∧
      IsDomainChart (H \ fillH (statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j))) c ∧
      IsCompact (statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j)) ∧
      IsHPHull (fillH (statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j))) ∧
      IsMapOut (fillH (statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j))) (fun z => c.1 z + (s₁' : ℂ)) ∧
      ContinuousOn gc Hbar ∧ EqOn gc c.2.1 H ∧ (∀ p ∈ Hbar, ‖gc p - p‖ ≤ Cg) ∧
      (∀ z, (gc ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧
      (0 : ℂ) ∈ statePhysicalSet 0
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j) ∧
      IsGeneratingTrace (D j).1 (D j).2 (LuM.trOf (D j)) ∧
      InjOn (LuM.trOf (D j)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2} ∧
      IsPreconnected (statePhysicalSet 0
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j) ∪
        gc '' (LuM.trOf (D j) '' Icc 0 (q : ℝ).toNNReal)) ∧
      ∃ T : Set ℂ, range β₀ = (statePhysicalSet 0
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j) ∪
          gc '' (LuM.trOf (D j) '' Icc 0 (q : ℝ).toNNReal)) ∪ T ∧
        IsPreconnected T ∧ ¬ Bornology.IsBounded T ∧ gc (LuM.trOf (D j) (q : ℝ).toNNReal) ∈ T ∧
        ∀ z ∈ T, z ∈ statePhysicalSet 0
            (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D j) ∪
          gc '' (LuM.trOf (D j) '' Icc 0 (q : ℝ).toNNReal) → z = gc (LuM.trOf (D j) (q : ℝ).toNNReal) := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  obtain ⟨σ₀, hσ₀⟩ := exists_between hs
  have hzH : β₀ σ₀ ∈ H := harc ⟨σ₀, hσ₀, rfl⟩
  have hzr : β₀ σ₀ ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D N) := hβr ▸ mem_range_self σ₀
  obtain ⟨j, hjN, θ', hl, hzt⟩ := exists_piece_of_mem_H hzr hzH
  set c := (ExplState.run κ b jumps w D j).2.2.2.2.1 with hcdef
  obtain ⟨s₁', gc, Cg, hD, hPc, hPh, hmo, hgc, hgi, hgb, hC', h0P, hcut⟩ :=
    Walk.walk_second_chart_inputs hW.1 hW.2 hreg hdN hβr hl hjN
  have hnd : stStatus (ExplState.run κ b jumps w D j) ≠ GW1Conn.stDone := Lx.stStatus_ne_done_of_launches w D hl
  have hgf := Walk.walk_finite_fibre hreg hinj htip hnd hD hgc hgi hgb
  have hl' : (ExplState.run κ b jumps w D (j + 1)).2.2.2.1 j ≠ none := by rw [hl]; exact Option.some_ne_none _
  have hPR := LuM.pieceRegular_of_launch hreg hl'
  have hα := LuM.isGeneratingTrace_trOf hPR
  obtain ⟨hW0, hWc, -⟩ := hPR
  have hinjα := hinj j hl'
  set α := LuM.trOf (D j) with hαdef
  have hWlt : ContinuousOn (D j).1 {s | (s : ℝ≥0∞) < (D j).2} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) < (D j).2) => show (s : ℝ≥0∞) ≤ (D j).2 from hs.le
  -- the tip set is the boundary-map image of the trace
  have htop : instrTime w j = ⊤ := Lx.instrTime_boundaryWalk_of_launch hl
  have hzt' : β₀ σ₀ ∈ gc '' (α '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2}) := by
    have h1 : (recPiece (ExplState.run κ b jumps w D j) (D j) (instrTime w j)).1.tipSet
        (recPiece (ExplState.run κ b jumps w D j) (D j) (instrTime w j)).2.1
        (recPiece (ExplState.run κ b jumps w D j) (D j) (instrTime w j)).2.2 =
        gc '' (α '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2}) := by
      show c.tipSet (fun r : ℝ≥0 => (D j).1 (min (r : ℝ≥0∞) (min (instrTime w j) (D j).2)).toNNReal)
        (min (instrTime w j) (D j).2) = _
      rw [htop, min_top_left]
      refine CounterflowRange.tipSet_stopped_eq_of_tendsto (f := gc) hα hWc hW0 fun t ht => ?_
      have hαH : α t ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hW0 ht
      refine ((hgc _ hαH).tendsto.mono_left (nhdsWithin_mono _ fun z hz =>
        le_of_lt (show (0 : ℝ) < z.im from hz))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz using hgi hz
    rw [← h1]; exact hzt
  obtain ⟨_, ⟨t₀, ht₀, rfl⟩, ht₀e⟩ := hzt'
  have hα₀ : α t₀ ∈ H := trace_mem_H_of_piece_mem_H hW hl hD hPc hgc hgi hα hW0 hWc ht₀ (ht₀e ▸ hzH)
  have ht₀0 : 0 < t₀ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h | h
    · rw [← h, hα.1] at hα₀
      exact absurd hα₀ (fun h0 => lt_irrefl (0 : ℝ) (show (0 : ℝ) < (0 : ℂ).im from h0))
    · exact h
  -- a rational earlier cut on the same arc
  have hφc : ContinuousOn (fun t => gc (α t)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2} :=
    hgc.comp hα.2.1 fun t ht => Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hW0 ht
  have hφr : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D j).2 → gc (α t) ∈ range β₀ := fun t ht => by
    obtain ⟨-, T, hr, -⟩ := hcut α hα t ht
    rw [hr]
    exact Or.inl (Or.inr ⟨α t, ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩, rfl⟩)
  obtain ⟨q, hq0, hqt, hφq⟩ := exists_rat_cut hβ hφc hφr ht₀ ht₀0 ⟨σ₀, hσ₀, ht₀e.symm⟩
  have hqζ : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D j).2 := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hqt) ht₀
  obtain ⟨τ, hτ, hτe⟩ := hφq
  have hαq : α (q : ℝ).toNNReal ∈ H :=
    trace_mem_H_of_piece_mem_H hW hl hD hPc hgc hgi hα hW0 hWc hqζ.le (hτe ▸ harc ⟨τ, hτ, rfl⟩)
  obtain ⟨hPc', hsplit⟩ := hcut α hα _ hqζ.le
  exact ⟨j, c, θ', q, s₁', Cg, gc, τ, hl, hq0, hqζ, hαq, hτ, hτe, hD, hPc, hPh, hmo, hgc, hgi, hC', hgf,
    h0P, hα, hinjα, hPc', hsplit⟩

end InteractingSLE.Theorem14.SB.S3.Asm
