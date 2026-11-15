/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BtInst
import InteractingSLE.Spec.Supplement.GW2TpRoot

/-!
# The owners' inputs of `nearImg`, as BUF consumes them

Packet PROVE-GW2-BUF (round 18). These are the statements the owners prove. BUF consumes them as stated (D17, D35).

* **`StageLawXStatement ver`** (STAGEMEAN/RELDET, D17 (B), the version form at every root). Almost surely on ROOTX's
  good set, a candidate's versions equal one canonical driver `Wc` before their caps. `Wc` is continuous from `0`,
  with a generating trace living to the root-`x` relative life `contactLifeX`, and the clock is bounded before the
  root-`x` contact. Round 17's `ae_gapVanishes_contactX_versions` turns this into the root-`x` contact clause.
* **`DeathThrXStatement ver ch`** (PROVE-GW2-NOTHR, D35 (D-a)). At a death clock (RELDET's `deathClockX`) before
  the relative life, the stage word of every instance whose cap is past the start has a continuation threshold along
  the canonical stage path at the death (the converse of `GW2Rz.NoThresholdX`, Theorem 1.3's `ζ = T_*` in the stage
  chart).
* **`BaseSigmaStatement base`** (PROVE-GW2-SDE, D35 (D-c)). The base word of the near selection is
  `c.sigma r l`-measurable up to null sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh

/-- **The canonical stage driver at one sample** (the stage law's version form at a root `x`): continuous from `0`,
equal to every version below its cap, with a generating trace living to the root-`x` relative life, the clock
bounded before contact. -/
def IsCanonX {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ξ : Ω)
    (Wc : ℝ≥0 → ℝ) : Prop :=
  Continuous Wc ∧ Wc 0 = 0 ∧ (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < V n ξ → R n q ξ = Wc q) ∧
    (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
      ENNReal.ofReal (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
        (schedTr c r l a ξ) (c.α ξ)) ≤ ζc) ∧
    ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ ≤ M

/-- **The stage law in version form at every root** (STAGEMEAN/RELDET, D17 (B)). -/
def StageLawXStatement (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GoodRoot c r → GW2Sdx.HistOrdered c r l →
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∃ Wc : ℝ≥0 → ℝ, IsCanonX c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc

/-- **The continuation threshold of a stage word along a stage path** (the form of `GW2Rz.NoThresholdX`). -/
def StageThreshold (κ : ℝ) (β : BoundaryWord) (D : ℝ≥0 → ℝ) (u : ℝ≥0) : Prop :=
  ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D u)
    (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -D v.toNNReal) (-flowLineXL β.fn β.jumps 0 i) u)
    (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => D v.toNNReal) (flowLineXR β.fn β.jumps 0 j) u)

/-- **The threshold at the death in the stage chart** (PROVE-GW2-NOTHR, D35 (D-a)): at a death clock before the
relative life, every canonical driver's stage path has, at the death, a continuation threshold of the stage word of
every instance whose cap is past its start. -/
def DeathThrXStatement (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (h : GoodRoot c r), GW2Sdx.HistOrdered c r l →
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∀ Wc : ℝ≥0 → ℝ, IsCanonX c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc →
      deathClockX c r l a ξ < ENNReal.ofReal (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)
        (schedW c r l a · ξ) (schedTr c r l a ξ) (c.α ξ)) →
      ∀ j : ℕ, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V j ξ →
        ∃ u : ℝ≥0, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) + u = deathClockX c r l a ξ ∧
          StageThreshold c.κ ((ch Ω c r l a).β ((instX h13 ver ch Ω c r l a j h.1).srecX c r l (rootPt r.1) ξ))
            (stgDrv Wc (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
              ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ)) u

/-- **The base word of the near selection is retained-measurable up to null sets** (PROVE-GW2-SDE, D35 (D-c)). -/
def BaseSigmaStatement
    (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), ∃ g : Ω → BoundaryWord, Measurable[c.sigma r l] g ∧
      ∀ᵐ ω ∂c.P, base Ω c r l ω = g ω

end InteractingSLE.Theorem14.GW2Bh
