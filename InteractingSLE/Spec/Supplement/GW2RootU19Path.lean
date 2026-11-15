/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootU19Shift

/-!
# Continuous physical carriers at every GW2 boundary root

Packet PROVE-T14-GW2ROOT2. Reuse the landed zero-root path construction
for the same driver family and translate its carrier. The canonical
staged law supplies the piece regularity from the source hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootU19

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

/-- A regular switched family from any real root has a continuous physical
carrier. Recentring reuses the existing concatenation proof. -/
theorem exists_path_physSet_sched (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (x : ℝ) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ, (ExplState.run κ b jumps (schedSpec x l) D (k + 1)).2.2.2.1 k =
      some (c, θ) → GW1P.PieceRegular (D k).1 (min (instrTime (schedSpec x l) k) (D k).2)) :
    ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = x ∧ MapsTo p (Icc 0 1) Hbar ∧
      ExplState.physSet κ b jumps (schedSpec x l) D = p '' Icc 0 1 := by
  have hreg0 : ∀ k c θ, (ExplState.run κ b jumps (schedSpec 0 l) D (k + 1)).2.2.2.1 k =
      some (c, θ) → GW1P.PieceRegular (D k).1 (min (instrTime (schedSpec 0 l) k) (D k).2) := by
    intro k c θ hl
    have hins := (eq_launch_of_launches (schedSpec 0 l) D hl).1
    change (scheduleProgram 0 l)[k]? = some (Sum.inl (θ, instrTime (schedSpec 0 l) k)) at hins
    have hk : k < (scheduleProgram 0 l).length := by
      by_contra hk
      have hn : (scheduleProgram 0 l)[k]? = none := List.getElem?_eq_none (not_lt.mp hk)
      rw [hn] at hins
      cases hins
    have hz := launches_run_gw2 (κ := κ) (b := b) (jumps := jumps)
      (spec := schedSpec 0 l) rfl (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk
    have hs : AllSucc (schedDelta 0 l) D k := by
      by_contra hs
      rw [hz.2 hs] at hl
      cases hl
    have hx := launches_run_gw2 (κ := κ) (b := b) (jumps := jumps)
      (spec := schedSpec x l) rfl (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk
    exact hreg k _ _ (hx.1 hs)
  obtain ⟨p, hp, hp0, hpH, hset⟩ := OwnHistoryPath.exists_path_prefixPhysSet_schedule
    (κ := κ) (b := b) (jumps := jumps) l D hreg0 (schedSpec 0 l).2.2.length
  refine ⟨fun t => p t + x, hp.add_const _, ?_, ?_, ?_⟩
  · change p 0 + x = x
    rw [hp0, zero_add]
  · intro t ht
    change 0 ≤ (p t + x).im
    simpa only [add_im, ofReal_im, add_zero] using hpH t ht
  · rw [physSet_sched_root_image, show ExplState.physSet κ b jumps (schedSpec 0 l) D =
        p '' Icc 0 1 from hset, image_image]

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- Actual canonical schedules have continuous physical carriers at every
real root, almost surely from the GFF law and Theorem 1.3. -/
theorem ae_exists_path_prefixSet (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (x : ℝ) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = x ∧
      MapsTo p (Icc 0 1) Hbar ∧ prefixSet hκ h12p βA b jumps c₀ h x l ω = p '' Icc 0 1 := by
  have hS := isStagedHistory_canonFam hκ h12p βA c₀
    (specAngle (schedSpec x l)) (specDelta (schedSpec x l))
    h13 hβA hb hc₀J hc₀ hh (spec := schedSpec x l) rfl
    (isFlowProg_spec x true l) (specDelta_ne_top _)
  have hR := stagedPiecesRegular_of_regular h13 hκ hb hS
    (fun k ω => isRegularDriver_canonDrive hκ h12p βA c₀ x
      (specAngle (schedSpec x l)) (specDelta (schedSpec x l)) (h ω) k)
  filter_upwards [hR.ae_pieceRegular] with ω hω
  exact exists_path_physSet_sched κ b jumps x l _ hω

/-- Every actual finite physical prefix is compact, lies in the closed
upper half-plane, and is attached to the lower half-plane at its root. -/
theorem ae_prefixSet_geometry (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (x : ℝ) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, IsCompact (prefixSet hκ h12p βA b jumps c₀ h x l ω) ∧
      IsPreconnected (prefixSet hκ h12p βA b jumps c₀ h x l ω ∪ {z : ℂ | z.im ≤ 0}) ∧
      prefixSet hκ h12p βA b jumps c₀ h x l ω ⊆ Hbar := by
  filter_upwards [ae_exists_path_prefixSet hκ h12p βA b jumps c₀ P h
    h13 hβA hb hc₀J hc₀ hh x l] with ω hω
  obtain ⟨p, hp, hp0, hpH, hset⟩ := hω
  rw [hset]
  refine ⟨isCompact_Icc.image_of_continuousOn hp, ?_, ?_⟩
  · apply (isPreconnected_Icc.image p hp).union (p 0)
      (mem_image_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num))
      (show (p 0).im ≤ 0 by rw [hp0, ofReal_im])
    exact (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
  · rintro z ⟨t, ht, rfl⟩
    exact hpH ht

end InteractingSLE.Theorem14.GW2TipSystem.RootU19
