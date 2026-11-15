/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfVersion
import InteractingSLE.Spec.Supplement.WalkSideInputs

/-!
# Theorem 1.4's walk leaves: the prefix chart has a version measurable in the capped past (input (B))

Packet PROVE-T14-WALKINF. **`prefixChartVersionStatement_of_mem`** proves PROVE-T14-WALKSIDE's named input
`WalkSide.PrefixChartVersionStatement θ right` for every angle `θ ∈ [−π/2, π/2]`, with no named input: the version is
the chart of the capped run read from its retained past (`verChart`, a measurable random chart for that past,
`isMeasChart_verChart`), and it is the run's chart almost surely on the capped launch event (`verChart_eq_run`: the
records of the launched pieces before `ℓ` are good because those pieces are continuous up to their stops, almost surely
by `StagedPiecesRegular`; the record of the capped piece is good because `τ` is before its lifetime). Deterministic
and measurability facts only; no Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.WalkInf

open Exist.Staged Exist.StagedLaw WalkSide

/-- **WALKSIDE's input (B): the prefix chart has a version measurable in the capped retained past**, for every angle
`θ ∈ [−π/2, π/2]` (no named input). -/
theorem prefixChartVersionStatement_of_mem {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) :
    PrefixChartVersionStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg ℓ τ
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  set cs := capSpec w ℓ θ (τ : ℝ≥0∞) with hcs
  have hEw := hE w hw
  have hRw := hR w hw
  obtain ⟨hconf, hlc, hharm, hdom, hfwd, hcb, hlift⟩ :=
    isMeasChart_verChart (κ := κ) (spec := cs) hb hEw.1 (hreg w) (ℓ + 1)
  refine ⟨verChart κ b jumps cs (E w) (ℓ + 1), hconf, hlc, hharm, hdom, hfwd, hcb, hlift, ?_⟩
  filter_upwards [hRw.ae_pieceRegular] with ω hω hcap
  -- the instruction `ℓ` is an unstopped angle-`θ` flow of the walk
  obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hcap.1
  obtain ⟨hins, -, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) w (fun j => E w j ω) hl
  obtain ⟨hθ', hT'⟩ := WalkLeaf.boundaryWalkSpec_inl hins
  rw [hT', hθ'] at hins
  have hℓ : ℓ < w.2.2.length := (List.getElem?_eq_some_iff.1 hins).1
  refine verChart_eq_run (fun j => hreg w j ω) (N := ℓ + 1) (fun j hj hlj hfin => ?_) (ℓ + 1) le_rfl
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · -- an earlier piece of the walk: continuous up to its stop
    rw [run_capSpec_of_le hℓ.le _ (Nat.succ_le_of_lt hj)] at hlj
    rw [instrTime_capSpec_of_lt hj hℓ.le] at hfin ⊢
    obtain ⟨⟨c', θ''⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hlj
    have hpr := hω j c' θ'' hl'
    exact isDrvGood_of_continuousOn_retOf (hreg w j ω) hfin
      (CounterflowRange.continuous_stopped hpr.2.1).continuousOn
  · -- the capped piece: `τ` is before its lifetime
    rw [instrTime_capSpec hℓ.le]
    exact isDrvGood_recOf_of_lt (hreg w j ω) hcap.2

end InteractingSLE.Theorem14.WalkInf
