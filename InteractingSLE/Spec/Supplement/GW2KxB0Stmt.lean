/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Set

/-!
# The root piece's kernel-side readings at index `0`, at a root `x` (statement for PROVE-GW2-RELDET, D62)

Packet PROVE-GW2-GEOM2, round 14 (D49, D62). One sample of the history `l = []` on success, with BR4a's datum at
index `0` (the launch chart `recenter x`, the counterflow `Wk` targeted at `x`, the clock `ℓ` up to the first tip at
`x`) and the instance's product-form no-contact reading up to the root piece's end `T`. The statement: the clock
reaches `s` at some `t₀`, the kernel tip at `t₀` is interior, and the root piece (its own trace `α`) has not touched the
inverted kernel counterflow `sphereInv γk` on `[0, t₀]` before `T`.

These are the inputs `ht₀`, `γk t₀ ∈ H` and `hcontact` of `sample_stage_read0X` and of the time-`T` form of
`ae_base_formsX`. They are the index-`0` analogues of the steps of `GW2Kx.sample_identity_rootX` (the clock's range,
`GW2Psm.trace_mem_H_of_tipAt`, `GW2Psm.lt_firstContactTime_launch` with the boundary extension `p ↦ p + x`, and
`GW2Kb.chosenTrace_eq_schedTr` for the root piece's trace up to `T`).

* **`SampleContactRoot0XStatement`** (named input; PROVE-GW2-RELDET proves it, D62).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw GW2Omx GW2Xk GW2Kb
open Supp8.GB6 (sphereInv firstContactTime)

/-- **The root piece's kernel-side readings at index `0`** (root `x ≥ 0`, one sample, success). -/
def SampleContactRoot0XStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) {ω : Ω},
    0 ≤ rootPt r.1 → oldSuccess c r [] ω →
    (∀ (j : ℕ) (hj : j < (futureProgram c r [] a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r [] a) ω ⟨j, hj⟩))) →
    (Continuous (stopDrv (specDelta (GW2Olm.futSpec c r [] a) 0) (GW2Olm.futFam c r [] a 0 ω)) ∧
      stopDrv (specDelta (GW2Olm.futSpec c r [] a) 0) (GW2Olm.futFam c r [] a 0 ω) 0 = 0) →
    IsRegularDriver (GW2Olm.futFam c r [] a 0 ω) →
    ∀ {α : ℝ≥0 → ℂ}, IsGeneratingTrace (fun t => (GW2Olm.futFam c r [] a 0 ω).1 t)
      (GW2Olm.futFam c r [] a 0 ω).2 α →
    Continuous (fun u => c.W u ω) → c.W 0 ω = 0 → IsGeneratingTrace (fun u => c.W u ω) ⊤ (c.α ω) →
    (∀ v : ℝ≥0, 0 < v → c.α ω v ≠ 0) → (c.s : ℝ≥0∞) < c.ζ ω → 0 < c.s → c.α ω c.s ∈ H →
    IsGeneratingTrace (fun u => GW2Rd.schedW c r [] a u ω) ⊤ (GW2Rd.schedTr c r [] a ω) →
    (∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r [],
      c.α ω v * ((rootPt r.1 : ℂ) + GW2Rd.schedTr c r [] a ω u) + 1 ≠ 0) →
    ∀ {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ}, Continuous Wk → Wk 0 = 0 → IsGeneratingTrace Wk ⊤ γk →
    (∀ q : ℝ≥0, 0 < q → γk q ≠ 0) →
    ∀ {ℓ : ℝ≥0 → ℝ≥0}, Continuous ℓ → StrictMono ℓ →
    range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      {((rootPt r.1 : ℝ) : ℂ)}} →
    (∀ (q : ℝ≥0) (z : ℂ), ((Chart.id.recenter (rootPt r.1)).trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) →
    ∃ t₀ : ℝ≥0, ℓ t₀ = c.s ∧ γk t₀ ∈ H ∧
      ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
        ((fun u => sphereInv (γk u : OnePoint ℂ)) '' Icc 0 t₀)

end InteractingSLE.Theorem14.GW2Kx
