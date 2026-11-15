/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NxFam
import InteractingSLE.Spec.Supplement.GW2NwDth

/-!
# BUF's `DeathThrX` at the stop-capped family

Packet PROVE-GW2-NOTHR (round 6, decision D54). The stop-capped family `GW2Nx.schedVerXStopFamily` (D49 (A)) has
both death-family inputs of round 5's `GW2Nv.deathThrX_of_export_fin`: caps strictly below the death clock
(`schedVerXStop_lt_deathClockX`, `hcaps`) and exhaustion below a finite death clock
(`schedVerXStop_exhausts_death`, `hD27`). So BUF's `DeathThrXStatement` (`GW2Nv.DeathThrXStatementN`) holds at the
SAME family as the `mean` statement (`GW2Nx.hmeanF_root0_stop`), from the death export alone:

* **`hD27_stop`**, **`hcaps_stop`**; **`deathThrX_stop`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nx

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  Sec5.Prop513Schedule

/-- **`hD27` of `GW2Nv.deathThrX_of_export_fin` for the stop family**: exhaustion below a finite death clock. -/
theorem hD27_stop (h13 : Exist.Theorem13Statement.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        deathClockX c r l a ω < ⊤ → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
          (schedVerXStopFamily h13 Ω c r l a).V n ω :=
  fun _ _ _ c r l a h hord => (schedVerXStop_exhausts_death h13 c r l a h.1 h.2 hord).mono
    fun _ hω hgood hold hlt => hω hgood hold hlt.ne

/-- **`hcaps` of `GW2Nv.deathThrX_of_export_fin` for the stop family**: caps strictly below the death clock. -/
theorem hcaps_stop (h13 : Exist.Theorem13Statement.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω →
        0 < candLife c r l a ω → ∀ n, (schedVerXStopFamily h13 Ω c r l a).V n ω < deathClockX c r l a ω :=
  fun _ _ _ c r l a h hord => schedVerXStop_lt_deathClockX h13 c r l a h.1 h.2 hord

/-- **BUF's `DeathThrXStatement` at the stop-capped family**, from the death export (round 5's
`GW2Nv.deathThrX_of_export_fin`). -/
theorem deathThrX_stop (h13 : Exist.Theorem13Statement.{u}) (ch : GW2Sdh.SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (ch Ω c r l a).β ∧
        (range fun y => Supp8.Q3Stop.wordType c.κ ((ch Ω c r l a).β y)).Countable ∧
        ∀ y, ((ch Ω c r l a).β y).IsSorted)
    (hexp : GW2Nv.DeathExportFamily h13 (schedVerXStopFamily h13) ch) :
    GW2Nv.DeathThrXStatementN h13 (schedVerXStopFamily h13) ch :=
  GW2Nv.deathThrX_of_export_fin h13 (schedVerXStopFamily h13) ch hword (hD27_stop h13) (hcaps_stop h13) hexp

end InteractingSLE.Theorem14.GW2Nx
