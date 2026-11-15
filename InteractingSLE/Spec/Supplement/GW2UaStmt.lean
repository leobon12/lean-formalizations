/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuStmt
import InteractingSLE.Spec.Supplement.GW2PsmCapB

/-!
# The stage law in version form, read on the curve stopped at the candidate's stop (decision D71)

Packet PROVE-GW2-RELDET (round 37, decision D71 (A)). BUF's `GW2Bh.StageLawXStatement` (landed, untouched) reads the
contact, the relative life and the clock bound of `GW2Bh.IsCanonX` on the whole explored curve. That includes the
frozen tail after the candidate's stop `T + candStop` (cap or death), which no flow-line fact controls. The stopped
form reads them on the explored curve STOPPED at the candidate's stop, i.e. at the times
`{t | t < contactX, t ≤ T + candStop}`:

* `stopLifeX`: the relative life of the stopped curve (the supremum of the root-`x` clock over those times);
* **`IsCanonXS`**: `IsCanonX` with the stopped life and the clock bound over those times;
* **`StageLawXSStatement h13 ver`**: almost surely on ROOTX's good set and the history's success, a canonical stopped
  driver exists.

BUF (`clock_lt_life`, `exhausts_below_min`) and NEARIMG2 (its uncapped law, caps → ∞) consume this form (D71). With the
stop family (D68; NOTHR's `schedVerXStopFamily`, versions at most the clock of `T + candStop`) the versions never reach
the frozen tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rv GW2Sde GW2Sdh

section Defs

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The relative life of the stopped curve**: the supremum of the root-`x` clock over the times before the root-`x`
contact and at most the candidate's stop `T + candStop`. -/
def stopLifeX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ξ : Ω) : ℝ :=
  sSup ((fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ''
    {t : ℝ≥0 | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ∧
      t ≤ RootJ31.historyTime c r l + GW2Psm.candStop c r l a ξ})

/-- **The canonical stage driver at one sample, read on the stopped curve** (`GW2Bh.IsCanonX` with the stopped life
and the clock bound before the contact and the stop): continuous from `0`, equal to every version below its cap, with
a generating trace living to the stopped relative life, the clock bounded before the contact and the stop. -/
def IsCanonXS (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ξ : Ω) (Wc : ℝ≥0 → ℝ) : Prop :=
  Continuous Wc ∧ Wc 0 = 0 ∧ (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < V n ξ → R n q ξ = Wc q) ∧
    (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧ ENNReal.ofReal (stopLifeX c r l a ξ) ≤ ζc) ∧
    ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      t ≤ RootJ31.historyTime c r l + GW2Psm.candStop c r l a ξ →
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ ≤ M

end Defs

/-- **The stage law in version form, on the curve stopped at the candidate's stop** (decision D71 (A); the successor
of `GW2Bh.StageLawXStatement` for BUF's `nearImg` and NEARIMG2's uncapped law). -/
def StageLawXSStatement (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∃ Wc : ℝ≥0 → ℝ, IsCanonXS c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc

end InteractingSLE.Theorem14.GW2Rd
