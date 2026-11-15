/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1DetLift
import InteractingSLE.Spec.Supplement.BW1TermMain

/-!
# GW1's `TerminalPathStatement` from Proposition BW1, without deterministic named inputs

Packet PROVE-BW1-DET. The assembly of `BW1Term.terminalPathStatement_of_bw1` with its two deterministic inputs
discharged:

* `TerminalPhysStatement` is proved (`BW1Det.terminalPhysStatement`, `BW1DetPhys`);
* `DetTerminalStatement` is replaced by the proved Borel relation graph (`BW1Det.termRelGraphStatement`) and the
  regularity of the post-piece counterflow from Theorem 1.3 (`BW1Det.ae_isTermRelOf_pos_graph`).

* **`ae_isTermRelOf_graph`**, **`terminalPathStatement_of_bw1_graph`**:
  `BW1.BW1Statement → Theorem12ParamStatement → Theorem13Statement → Theorem13Statement.{0} → TerminalPathStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Det

open Exist Exist.StagedLaw Exist.Staged GW1RestartPair BW1Term

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Almost surely at a next launch, the canonical post-piece counterflow is regular and is the relative counterflow
of the launch counterflow after the piece.** -/
theorem ae_isTermRelOf_graph (hBW1 : BW1.BW1Statement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E right n V ζV ℓ) {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞}
    (hQ : GW1Laws.IsTerminalRestartCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q ζQ)
    (hQreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ζQ ω = ⊤ ∧ Continuous (fun t => Q t ω) ∧ Q 0 ω = 0) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      GW1Path.IsRegCf (fun t => Q t ω) ∧
        IsTermRelOf (fun t => Q t ω) (fun t => V t ω) (E (GW1Z.walkSpec b jumps right) (2 * n) ω) := by
  filter_upwards [ae_isTermRelOf_pos_graph hBW1 h12p hT13 hT13₀ hdata hQ hQreg,
    ae_isTermRelOf_zero h12p hT13 hT13₀ hdata hQ hQreg] with ω h1 h2 hn
  by_cases hz : (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2 = 0
  · exact h2 hn hz
  · exact h1 hn hz

end Main

/-- **GW1's `TerminalPathStatement` from Proposition BW1** (conditional helper): Proposition BW1 in its source form
for one flow piece (`BW1.BW1Statement`), Theorem 1.2 (R44 form) and Theorem 1.3. No deterministic named input: the
Borel relation graph (`termRelGraphStatement`) and the physical reading (`terminalPhysStatement`) are proved, and the
regularity of the post-piece counterflow comes from Theorem 1.3 under the conditional laws. -/
theorem terminalPathStatement_of_bw1_graph (hBW1 : BW1.BW1Statement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) :
    GW1Laws.TerminalPathStatement.{u} := by
  classical
  intro κ b jumps Ω _ _ P _ h W' ζ' E right n V ζV ℓ hdata Q ζQ hcond _ hQreg
  have hκ := hdata.pos
  have hκ4 := hdata.lt_four
  have hb := hdata.boundary
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hreg := hdata.regular (GW1Z.walkSpec b jumps right)
  have hRp := hdata.pieces _ hprog
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hdata.stages, hRp] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  refine ⟨fun ω => if hx : IsTermRelOf (fun t => Q t ω) (fun t => V t ω)
      (E (GW1Z.walkSpec b jumps right) (2 * n) ω) then hx.choose else id, ?_⟩
  filter_upwards [ae_isTermRelOf_graph hBW1 h12p hT13 hT13₀ hdata hcond hQreg, hQreg, hdata.current.2.2, hprev,
    hdata.stages, hRp] with ω hr hq hcl hpv hst hpc hn
  obtain ⟨hQr, hrelω⟩ := hr hn
  obtain ⟨hζ, hQc, hQ0⟩ := hq hn
  have hl := hpv hn
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨hc_eq, -⟩ := launch_record_walk hcθ
  obtain ⟨-, hVc, hV0, hVtr, -, -, hrange, htip⟩ := hcl c θ hcθ
  refine ⟨hζ, hQc, hQ0, hQr.2.2, ?_⟩
  -- the launch counterflow never visits the old union
  have havoid : ∀ (r : ℝ≥0) (z : ℂ), ((stChart (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n))).trans infinitySourceChart).tipAt (fun t => V t ω) r z →
      z ∉ SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * n) := by
    intro r z hz hmem
    rw [← hc_eq] at hz
    have hW := (htip r z).1 hz
    have hlt : ((ℓ ω r : ℝ≥0) : ℝ≥0∞) < firstTipTime infinitySourceChart (fun t => W' t ω)
        (SB.prefixPhysSet κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
          (2 * n)) := by
      have hm := mem_range_self (f := ℓ ω) r
      rw [hrange] at hm
      exact hm
    exact absurd (iInf₂_le (ℓ ω r) ⟨z, hmem, hW⟩) (not_le.2 hlt)
  have hpieces : ∀ k c' θ', (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (k + 1)).2.2.2.1 k = some (c', θ') →
      GW1P.PieceRegular (E (GW1Z.walkSpec b jumps right) k ω).1
        (min (instrTime (GW1Z.walkSpec b jumps right) k) (E (GW1Z.walkSpec b jumps right) k ω).2) :=
    fun k c' θ' hl' => hpc k θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  show IsRetainedClock _ _ _ _ _ (if hx : IsTermRelOf (fun t => Q t ω) (fun t => V t ω)
    (E (GW1Z.walkSpec b jumps right) (2 * n) ω) then hx.choose else id)
  split_ifs
  obtain ⟨hℓc, hℓm, hℓr, hℓt⟩ := hrelω.choose_spec
  exact terminalPhysStatement κ hκ hκ4 b jumps hb right (fun j => E (GW1Z.walkSpec b jumps right) j ω)
    (fun k => hreg k ω) hst hpieces n hn (fun t => V t ω) (fun t => Q t ω) ⟨hVc, hV0, hVtr⟩ hQr havoid _ hℓc hℓm hℓr hℓt

end InteractingSLE.Theorem14.BW1Det
