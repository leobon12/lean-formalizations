/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NiUnc

/-!
# The uncapped stage law read on the curve stopped at its death (D82)

Packet PROVE-GW2-NEARIMG2, decision D82 item 1. `GW2Ni.IsCanonUX` reads the uncapped curve over its whole contact
life: the trace clause asks for a trace living to `contactLifeX` and the clock clause for a bound on every `t` before
the contact. When the uncapped piece dies before the contact, both read the **frozen tail after the death**. This is
the same issue as RELDET's round 36 for the capped law. The clock bound before the contact then says that the frozen
tail does not first meet the retained prefix at its tip, and the stopped capped law (D71) does not control that tail.

This file states the uncapped law in the stopped form of D71. The life and the clock bound are read on
`{t < contact, t ≤ T + uncLife}` (the uncapped curve stopped at its death; `T + ⊤ = ⊤` when it never dies). The hull
identity is unchanged (it is only asked below the death clock).

* `uncStopLifeX`, **`IsCanonUXS`**, **`StageLawUXSStatement`**;
* `IsCanonUX.isCanonUXS`: the unstopped form gives the stopped one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

section Defs

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

/-- **The stopped set of the uncapped curve**: before the root-`x` contact and up to the death. -/
def uncStopSet (ξ : Ω) : Set ℝ≥0 :=
  {t | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ ∧
    (t : ℝ≥0∞) ≤ (historyTime c r l : ℝ≥0∞) + uncLife c r l i ξ}

/-- **The relative life of the uncapped curve stopped at its death.** -/
def uncStopLifeX (ξ : Ω) : ℝ :=
  sSup ((fun t => clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ) '' uncStopSet c r l i ξ)

/-- **The uncapped stage law at one sample, read on the curve stopped at its death**: `IsCanonUX` with the trace
living to the stopped life and the clock bounded on the stopped set. -/
def IsCanonUXS (ξ : Ω) (Wc : ℝ≥0 → ℝ) : Prop :=
  Continuous Wc ∧ Wc 0 = 0 ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ) < uncDeathX c r l i ξ →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ) ∧
    (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
      ENNReal.ofReal (uncStopLifeX c r l i ξ) ≤ ζc) ∧
    ∃ M : ℝ, ∀ t ∈ uncStopSet c r l i ξ, clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ ≤ M

end Defs

/-- **The uncapped stage law, stopped at the death** (on the good counterflow records and the history's success). -/
def StageLawUXSStatement : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (i : ℕ), GW2Rv.GoodRoot c r → GW2Sdx.HistOrdered c r l →
    ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ξ →
      ∃ Wc : ℝ≥0 → ℝ, IsCanonUXS c r l i ξ Wc

section Weaken

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

/-- **The unstopped form gives the stopped one** when the curve lives forever: the stopped set is everything before
the contact. -/
theorem IsCanonUX.isCanonUXS_of_top {ξ : Ω} {Wc : ℝ≥0 → ℝ} (h : IsCanonUX c r l i ξ Wc)
    (hℓ : uncLife c r l i ξ = ⊤) : IsCanonUXS c r l i ξ Wc := by
  obtain ⟨hWc, hWc0, hK, ⟨ζc, ηc, hη, hL⟩, M, hM⟩ := h
  have hset : uncStopSet c r l i ξ =
      {t : ℝ≥0 | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ} := by
    ext t
    simp only [uncStopSet, hℓ, add_top, le_top, and_true, mem_ofPred_eq]
  refine ⟨hWc, hWc0, hK, ⟨ζc, ηc, hη, ?_⟩, M, fun t ht => hM t ?_⟩
  · unfold uncStopLifeX
    rw [hset]
    exact hL
  · rw [hset] at ht
    exact ht

/-- **Before a death after the contact, the stopped form is the unstopped one**: if every time before the contact is
before the death (the contact comes first, or the curve never dies), `IsCanonUXS` gives `IsCanonUX`. -/
theorem IsCanonUXS.isCanonUX_of_le {ξ : Ω} {Wc : ℝ≥0 → ℝ} (h : IsCanonUXS c r l i ξ Wc)
    (hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ →
      (t : ℝ≥0∞) ≤ (historyTime c r l : ℝ≥0∞) + uncLife c r l i ξ) : IsCanonUX c r l i ξ Wc := by
  obtain ⟨hWc, hWc0, hK, ⟨ζc, ηc, hη, hL⟩, M, hM⟩ := h
  have hset : uncStopSet c r l i ξ =
      {t : ℝ≥0 | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ} := by
    ext t
    simp only [uncStopSet, mem_ofPred_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hle t h⟩⟩
  refine ⟨hWc, hWc0, hK, ⟨ζc, ηc, hη, ?_⟩, M, fun t ht => hM t ?_⟩
  · unfold uncStopLifeX at hL
    rw [hset] at hL
    exact hL
  · rw [hset]
    exact ht

end Weaken

end InteractingSLE.Theorem14.GW2Ni
