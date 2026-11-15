/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FzData
import InteractingSLE.Spec.Supplement.SB2ZsJx

/-!
# SB2ZsData: `SB2FzData` for the lifetime-generic line version `SB2LineVersionG`

Packet PROVE-T14-SB2DRV (round 15, decision D4: SB2(1) at announced stops). The declarations of `SB2FzData` that
depend on the line version, for `SB2LineVersionG` (guards `a t < Λ w` in place of `a t < thr`), with the suffix `G`.
The proofs are the landed ones with the guard replaced. No source theorem is replaced.
-/
/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/

/-!
# SB2(1)'s late (S) line mean, part 16: FIN's configuration data chosen at every sample

Packet PROVE-T14-SB2DRV (round 12). FIN's union mean takes its configuration data as functions of the sample. The
configuration of `ae_relConfigJK_line_of_tip` (exploration word = the flow-line word, `χ = chiC κ`) is packaged:

* **`FinCfgData`**: the eight components (relative driver and trace, exploration driver and trace, the chart's
  log-derivative lift, the three bounded harmonic extensions);
* **`IsFinCfg`**: the configuration predicate of `ae_relConfigJK_line_of_tip` at one sample;
* **`ae_exists_isFinCfg`**: almost surely on the live cell after the entrance some data satisfy it (from the named
  hypothesis `SB2JxTipStatement`);
* **`finCfg`**, **`isFinCfg_finCfg`**: a choice (`Classical.epsilon`) satisfying it wherever some data do.

**R48.** Theorems 1.2–1.3 are not used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6
open Supp8.Q3Chain (flowedData flowedJumps initJumps)

section Data

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ} {I : K2LaunchInputs κ b jumps P h E k u ψ} {u₀ : ℂ → ℝ}
  {D : EntranceUnion κ b jumps P h E k u η ζ u₀}

/-- **FIN's configuration predicate at one sample** (the conclusion of `ae_relConfigJK_line_of_tip` with the
flow-line exploration word and `χ = chiC κ`). -/
def IsFinCfgG (Vd : SB2LineVersionG HP I D) (wt : WordType) (t : ℝ≥0) (A' : Ω → Set ℂ) (ω : Ω)
    (d : FinCfgData) : Prop :=
  (∀ q : ℝ≥0, (q : ℝ≥0∞) <
    Vd.Λ wt ω →
    Vd.W q ω = d.Wr q) ∧
  (∃ t₂ : ℝ, (t : ℝ) < t₂ ∧ ∀ r : ℝ, 0 ≤ r → r < t₂ → d.ηw r = η ω r.toNNReal - u) ∧ Vd.a t ω ≠ ⊤ ∧
  EqOn (Lw.shiftChart (I.chart ω) u 0).2.2 (fun z => (d.LΨ z).im)
    (H \ (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω) ∧
  FinRel.IsRelConfigJK ((fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω)
    (Lw.shiftChart (I.chart ω) u 0).1 (Lw.shiftChart (I.chart ω) u 0).2.1 d.LΨ ∅ d.w d.Wr d.ηw d.ηr t
    ((Vd.a t ω).toNNReal : ℝ) (chiC κ) (Real.pi / Real.sqrt κ)
    (forceBoundaryData κ (typedRhoL wt) (typedRhoR wt) (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω))
    (flowedData κ (flowLineRhoL κ b jumps u ψ) (flowLineRhoR κ b jumps u ψ) (flowLineXL b jumps u)
      (flowLineXR b jumps u) d.w t)
    (flowedData κ (typedRhoL wt) (typedRhoR wt) (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω) d.Wr
      ((Vd.a t ω).toNNReal : ℝ))
    (initJumps (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω))
    (flowedJumps (flowLineXL b jumps u) (flowLineXR b jumps u) d.w t)
    (flowedJumps (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω) d.Wr ((Vd.a t ω).toNNReal : ℝ)) d.G₀ d.GE d.G
    (fun z => d.G (fwdMap d.Wr ((Vd.a t ω).toNNReal : ℝ) ((Lw.shiftChart (I.chart ω) u 0).1 z)) -
      chiC κ * ((logDerivFwd d.Wr ((Vd.a t ω).toNNReal : ℝ) ((Lw.shiftChart (I.chart ω) u 0).1 z)).im +
        (d.LΨ z).im))
/-- **The chosen configuration data** at one sample. -/
def finCfgG (Vd : SB2LineVersionG HP I D) (wt : WordType) (t : ℝ≥0) (A' : Ω → Set ℂ) (ω : Ω) : FinCfgData :=
  Classical.epsilon (IsFinCfgG Vd wt t A' ω)
theorem isFinCfg_finCfgG (Vd : SB2LineVersionG HP I D) (wt : WordType) (t : ℝ≥0) (A' : Ω → Set ℂ) {ω : Ω}
    (hω : ∃ d, IsFinCfgG Vd wt t A' ω d) : IsFinCfgG Vd wt t A' ω (finCfgG Vd wt t A' ω) :=
  Classical.epsilon_spec hω
end Data

end InteractingSLE.Theorem14.SB.Lv

