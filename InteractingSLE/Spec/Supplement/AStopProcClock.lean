/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverObservable
import InteractingSLE.Spec.Restart.RetPlumbProofDriverLife
import InteractingSLE.Spec.Restart.RetPlumbProofInputsSafe

/-!
# A-stopped processes of an abstract chart path: clock, lifetime, trace and driver

Packet PROVE-T15-ASTOP-PROC (items 2–3 of `RLC.OrdModel.AStopSourceInputs`). RETPLUMB's processes (`retClock`,
`retLife`, `retPath`, `retDriver`) are hard-wired to the stop set `A ∪ ℝ` and to disjoint pairs. Here they are rebuilt
for an abstract chart path `Γ ω` in physical time with physical lifetime `L ω` (in the application: the chart path of
a continuation stopped at its first new contact with `A`, `Supp7.contPath`):

* `aClock Γ t ω` (the relative capacity reached at physical time `t`, regularized off good samples),
  `aLife Γ L ω` (the capacity lifetime), `aPath Γ L ω` (the chart path in capacity time) and `aDriver Γ L`
  (a generating driver where one exists);
* `IsAGood Γ L ω`: the pathwise facts a retained continuation gives (`Supp7.IsRetCont`);
* the pathwise clock facts `IsAGood.aClock_eq`, `aClock_lt_aLife_iff`, `aClock_le_aLife`, `exists_aClock_ge`.

The measurable part (observations, time change, adapted driver) is in `AStopProcAdapt`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Restart.RetAux79 Supp7

variable {Ω : Type*}

/-! ### The processes -/

section Defs

open scoped Classical in
/-- **The clock**: the capacity reached by the chart path at physical time `t` (regularized to `0` when the relative
capacity clock is not continuous, monotone and `0` at `0`). -/
def aClock (Γ : Ω → ℝ≥0 → ℂ) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if Continuous (chartClock (Γ ω)) ∧ Monotone (chartClock (Γ ω)) ∧ chartClock (Γ ω) 0 = 0 then
    (chartClock (Γ ω) t).toNNReal
  else 0

/-- **The capacity lifetime** of the chart path on the physical lifetime `L`. -/
def aLife (Γ : Ω → ℝ≥0 → ℂ) (L : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := capLife (chartClock (Γ ω)) (L ω)

/-- **The chart path in capacity time.** -/
def aPath (Γ : Ω → ℝ≥0 → ℂ) (L : Ω → ℝ≥0∞) (ω : Ω) (q : ℝ≥0) : ℂ :=
  Γ ω (invClock (chartClock (Γ ω)) (L ω) q)

/-- A continuous driver from `0` generating the chart path in capacity time up to the capacity lifetime. -/
def IsAGen (Γ : Ω → ℝ≥0 → ℂ) (L : Ω → ℝ≥0∞) (ω : Ω) (W : ℝ≥0 → ℝ) : Prop :=
  Continuous W ∧ W 0 = 0 ∧ IsGeneratingTrace W (aLife Γ L ω) (aPath Γ L ω)

open scoped Classical in
/-- **The driver process**: a generating driver where one exists, `0` otherwise. -/
def aDriver (Γ : Ω → ℝ≥0 → ℂ) (L : Ω → ℝ≥0∞) (q : ℝ≥0) (ω : Ω) : ℝ :=
  if h : ∃ W, IsAGen Γ L ω W then h.choose q else 0

variable {Γ : Ω → ℝ≥0 → ℂ} {L : Ω → ℝ≥0∞}

theorem isAGen_aDriver {ω : Ω} (h : ∃ W, IsAGen Γ L ω W) : IsAGen Γ L ω fun q => aDriver Γ L q ω := by
  have e : (fun q => aDriver Γ L q ω) = h.choose := by
    funext q
    simp only [aDriver, h, ↓reduceDIte]
  rw [e]
  exact h.choose_spec

theorem continuous_aDriver (ω : Ω) : Continuous fun q => aDriver Γ L q ω := by
  by_cases h : ∃ W, IsAGen Γ L ω W
  · exact (isAGen_aDriver h).1
  · have e : (fun q => aDriver Γ L q ω) = fun _ => 0 := by
      funext q
      simp only [aDriver, h, ↓reduceDIte]
    rw [e]
    exact continuous_const

theorem aDriver_zero (ω : Ω) : aDriver Γ L 0 ω = 0 := by
  by_cases h : ∃ W, IsAGen Γ L ω W
  · exact (isAGen_aDriver h).2.1
  · simp only [aDriver, h, ↓reduceDIte]

end Defs

/-! ### Pathwise good samples -/

/-- **The pathwise facts of a good sample** (those of a retained continuation, `Supp7.IsRetCont`): the chart path is
continuous from `0` and constant after the physical lifetime, its relative capacity is a continuous monotone clock on
the physical lifetime, and a continuous driver from `0` generates it in capacity time. -/
structure IsAGood (Γ : Ω → ℝ≥0 → ℂ) (L : Ω → ℝ≥0∞) (ω : Ω) : Prop where
  pos : 0 < L ω
  cont : Continuous (Γ ω)
  zero : Γ ω 0 = 0
  clock : IsClockOn (chartClock (Γ ω)) (L ω)
  mono : Monotone (chartClock (Γ ω))
  contClock : Continuous (chartClock (Γ ω))
  const : ∀ s : ℝ≥0, L ω ≤ s → Γ ω s = Γ ω (L ω).toNNReal
  gen : ∃ W, IsAGen Γ L ω W

namespace IsAGood

variable {Γ : Ω → ℝ≥0 → ℂ} {L : Ω → ℝ≥0∞} {ω : Ω} (hg : IsAGood Γ L ω)
include hg

theorem aClock_eq (t : ℝ≥0) : aClock Γ t ω = (chartClock (Γ ω) t).toNNReal := by
  have hc : Continuous (chartClock (Γ ω)) ∧ Monotone (chartClock (Γ ω)) ∧ chartClock (Γ ω) 0 = 0 :=
    ⟨hg.contClock, hg.mono, hg.clock.zero⟩
  unfold aClock
  simp only [hc, and_self, ↓reduceIte]

theorem chartClock_nonneg (s : ℝ≥0) : 0 ≤ chartClock (Γ ω) s := by
  rw [← hg.clock.zero]
  exact hg.mono (zero_le : (0 : ℝ≥0) ≤ s)

theorem coe_aClock (s : ℝ≥0) : (aClock Γ s ω : ℝ) = chartClock (Γ ω) s := by
  rw [hg.aClock_eq]
  exact Real.coe_toNNReal _ (hg.chartClock_nonneg s)

/-- **Survival can be tested in physical time.** -/
theorem aClock_lt_aLife_iff {t : ℝ≥0} : (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω ↔ (t : ℝ≥0∞) < L ω := by
  rw [hg.aClock_eq]
  exact ⟨lt_of_toNNReal_lt_capLife hg.mono, coe_toNNReal_lt_capLife hg.clock⟩

/-- **The clock never exceeds the capacity lifetime.** -/
theorem aClock_le_aLife (t : ℝ≥0) : (aClock Γ t ω : ℝ≥0∞) ≤ aLife Γ L ω := by
  rw [hg.aClock_eq]
  by_cases ht : (t : ℝ≥0∞) ≤ L ω
  · exact hg.clock.coe_toNNReal_le_capLife ht
  · have hLt : L ω ≤ (t : ℝ≥0∞) := (lt_of_not_ge ht).le
    have hfin : L ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hLt
    have he : ((L ω).toNNReal : ℝ≥0∞) = L ω := ENNReal.coe_toNNReal hfin
    have hc : ∀ s, (L ω).toNNReal ≤ s → Γ ω s = Γ ω (L ω).toNNReal := fun s hs =>
      hg.const s (he ▸ ENNReal.coe_le_coe.2 hs)
    rw [chartClock_eq_of_constant_after hc (ENNReal.coe_le_coe.1 (he.symm ▸ hLt))]
    exact hg.clock.coe_toNNReal_le_capLife he.le

/-- **Every capacity before the capacity lifetime is reached by the clock.** -/
theorem exists_aClock_ge {q : ℝ≥0} (hq : (q : ℝ≥0∞) < aLife Γ L ω) : ∃ t, q ≤ aClock Γ t ω := by
  obtain ⟨t, ht⟩ := exists_le_toNNReal_of_lt_capLife hg.clock hq
  exact ⟨t, by rw [hg.aClock_eq]; exact ht⟩

/-- **A capacity before the capacity lifetime is reached before the physical lifetime.** -/
theorem lt_of_aClock_lt {t : ℝ≥0} (ht : (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω) : (t : ℝ≥0∞) < L ω :=
  hg.aClock_lt_aLife_iff.1 ht

end IsAGood

/-- **Good samples only depend on the chart path and the lifetime at the sample.** -/
theorem IsAGood.congr {Γ Γ' : Ω → ℝ≥0 → ℂ} {L L' : Ω → ℝ≥0∞} {ω : Ω} (hg : IsAGood Γ L ω)
    (hΓ : Γ' ω = Γ ω) (hL : L' ω = L ω) : IsAGood Γ' L' ω := by
  have hl : aLife Γ' L' ω = aLife Γ L ω := by unfold aLife; rw [hΓ, hL]
  have hp : aPath Γ' L' ω = aPath Γ L ω := by funext q; unfold aPath; rw [hΓ, hL]
  obtain ⟨hpos, hc, h0, hclk, hm, hcc, hconst, W, hW⟩ := hg
  refine ⟨hL ▸ hpos, hΓ ▸ hc, hΓ ▸ h0, hΓ ▸ hL ▸ hclk, hΓ ▸ hm, hΓ ▸ hcc, fun s hs => ?_, W, ?_⟩
  · rw [hΓ, hL]
    exact hconst s (hL ▸ hs)
  · refine ⟨hW.1, hW.2.1, ?_⟩
    rw [hl, hp]
    exact hW.2.2

/-- **A retained continuation gives a good sample** (`Supp7.IsRetCont`: the chart path of the continuation stopped at
its first new contact with `O ∪ η([0, a])`, and `RetAux79.canonRetPath_facts` for the generating driver). -/
theorem isAGood_of_isRetCont {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}
    (hR : IsRetCont η ζ x a O φ ψ) (ω : Ω) :
    IsAGood (fun _ : Ω => contPath (QuantumZipper.H \ fillH (O ∪ η '' Icc 0 a)) φ η a
        (contLife η ζ a (O ∪ η '' Icc 0 a)))
      (fun _ : Ω => contLife η ζ a (O ∪ η '' Icc 0 a)) ω := by
  obtain ⟨W, hWc, hW0, hgen, -⟩ := canonRetPath_facts hR
  refine ⟨hR.pos_contLife, hR.continuous_contPath, hR.contPath_zero, hR.isClockOn,
    monotone_chartClock_of_isRetCont hR, hR.continuous_chartClock, fun s hs => ?_, W, hWc, hW0, ?_⟩
  · have hfin : contLife η ζ a (O ∪ η '' Icc 0 a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hs
    rw [contPath_of_le hs, contPath_of_le (ENNReal.coe_toNNReal hfin).ge]
  · rw [canonRetLife_zero, canonRetPath_zero] at hgen
    exact hgen

end InteractingSLE.RLC.AStopProc
