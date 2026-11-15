/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSideResumeCap
import InteractingSLE.Spec.Supplement.WalkSide2

/-!
# The unrestricted walk-prefix locality inputs from non-launch at non-flow indices

Packet PROVE-T14-WALKSIDE2, continuation. The exact unrestricted locality inputs
are reduced to `NonFlowCapNoLaunchStatement`, the remaining mathematical input:
at an index that is not an original flow instruction, replacing that instruction
(or appending at the end) by a time-zero flow never launches almost surely.
The launch decision is independent of own time, so this suffices for every cap.
Indices beyond the program are handled by truncating their index to its length.

This file does not prove `NonFlowCapNoLaunchStatement`. It appears explicitly as
a hypothesis of each conditional locality theorem. The original statements and
the already-landed modules are unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkSideResume

open LocalSets Exist.Staged Exist.StagedLaw WalkSide

/-- The remaining non-launch input, under exactly the walk-prefix setting.
Only non-flow indices up to and including the program's end are tested. No own-time
parameter is needed: the launch decision is independent of that time. -/
def NonFlowCapNoLaunchStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), IsRegularDriver (E spec k ω)) →
    ∀ ℓ : ℕ, ℓ ≤ (boundaryWalkSpec b jumps θ right).2.2.length →
      (boundaryWalkSpec b jumps θ right).2.2[ℓ]? ≠ some (Sum.inl (θ, ⊤)) →
      ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ 0)
          (fun j => E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.1 ℓ = none

/-- Capping beyond the program is the same program as capping at its end. -/
theorem capSpec_eq_capSpec_min (w : ExplSpec) (ℓ : ℕ) (θ : ℝ) (τ : ℝ≥0∞) :
    capSpec w ℓ θ τ = capSpec w (min ℓ w.2.2.length) θ τ := by
  by_cases hℓ : ℓ ≤ w.2.2.length
  · rw [min_eq_left hℓ]
  · simp only [capSpec, min_eq_right (not_le.1 hℓ).le,
      List.take_of_length_le (not_le.1 hℓ).le, List.take_length]

/-- Conditional proof of the exact unrestricted prefix-locality input. The new
non-launch hypothesis is used only where the original instruction is not a flow. -/
theorem prefixMarkedLocalStatement_of_noLaunch
    (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool}
    (hN : NonFlowCapNoLaunchStatement.{u} θ right) :
    WalkSide.PrefixMarkedLocalStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg u₀ hu₀ ℓ τ
  let w := boundaryWalkSpec b jumps θ right
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  let n := min ℓ w.2.2.length
  have hn : n ≤ w.2.2.length := min_le_right _ _
  by_cases hflow : w.2.2[n]? = some (Sum.inl (θ, ⊤))
  · have hnlt : n < w.2.2.length := (List.getElem?_eq_some_iff.1 hflow).1
    have hnℓ : n = ℓ := by
      dsimp only [n] at hnlt ⊢
      omega
    rw [hnℓ] at hflow hnlt
    exact WalkInf.prefixMarkedLocalOnStatement_of_thm12_thm13 h12p h13 hθ right
      κ hκ hκ4 b jumps hb P h hh E hE hR hreg u₀ hu₀ ℓ τ hnlt hflow
  · have hN0 := hN κ hκ hκ4 b jumps hb P h hh E hE hR hreg n hn hflow
    have hNτ : ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (capSpec w n θ (τ : ℝ≥0∞))
          (fun j => E w j ω) (n + 1)).2.2.2.1 n = none := by
      filter_upwards [hN0] with ω hω
      rw [congrFun (launches_capSpec_time_indep (κ := κ) (b := b) (jumps := jumps)
        (θ := θ) hn (fun j => E w j ω) (τ : ℝ≥0∞) 0) n]
      exact hω
    rw [capSpec_eq_capSpec_min w ℓ θ (τ : ℝ≥0∞)]
    exact markedLocal_capSpec_of_noLaunch h12p h13 hκ hκ4 hb hh (hE w hw) (hreg w)
      (fun _ _ _ ht => WalkLeaf.boundaryWalkSpec_inl ht) hn u₀ hu₀ hNτ (ℓ + 1)

/-- The exact right-walk locality leaf, conditional on the explicit non-launch input. -/
theorem prefixMarkedLocalStatement_right_of_noLaunch
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hN : NonFlowCapNoLaunchStatement.{u} (-(Real.pi / 2)) true) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true :=
  prefixMarkedLocalStatement_of_noLaunch
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    ⟨le_rfl, by linarith only [Real.pi_pos]⟩ hN

/-- The exact left-walk locality leaf, conditional on the explicit non-launch input. -/
theorem prefixMarkedLocalStatement_left_of_noLaunch
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hN : NonFlowCapNoLaunchStatement.{u} (Real.pi / 2) false) :
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false :=
  prefixMarkedLocalStatement_of_noLaunch
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    ⟨by linarith only [Real.pi_pos], le_rfl⟩ hN

/-- All four original packet leaves, with the remaining mathematics visible as
two non-launch hypotheses. The chart-version leaves have no extra hypotheses. -/
theorem prefixInputs_of_noLaunch
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hNR : NonFlowCapNoLaunchStatement.{u} (-(Real.pi / 2)) true)
    (hNL : NonFlowCapNoLaunchStatement.{u} (Real.pi / 2) false) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false ∧
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  ⟨prefixMarkedLocalStatement_right_of_noLaunch h12 h13 hNR,
    WalkSide2.prefixChartVersionStatement_right,
    prefixMarkedLocalStatement_left_of_noLaunch h12 h13 hNL,
    WalkSide2.prefixChartVersionStatement_left⟩

end InteractingSLE.Theorem14.WalkSideResume
