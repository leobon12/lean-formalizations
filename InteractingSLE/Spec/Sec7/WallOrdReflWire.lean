/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.WallOrdReflInf
import InteractingSLE.Spec.Sec7.R5PhaseTest

/-!
# `R5Lift.R7OuterRefl(Inf)` for R.5's shifted pocket charts

Packet PROVE-WALL-ORDER, target (3), wiring. `R5Wall.TwoSeedSplitInputFresh(Inf)` (`R5LfFreshSplit.lean`) asks, per
test `A` and capacity `q`, for `R5Lift.R7OuterRefl(Inf)` with the chart `shiftChart (pChart A C ψ ω) (n ω)` and an
exceptional set `X q ⊇ outerExc(Inf)` (which the bundle already requires). **`r7OuterRefl_shift`**,
**`r7OuterReflInf_shift`** supply it from the pocket configuration and the Jordan coordinate alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.WallOrd

open PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen PocketStopField R5Phase

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {A : Set Ω} {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
  {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}

/-- **`R5Lift.R7OuterRefl` for the shifted pocket chart** (bounded reverse-contained pocket). -/
theorem r7OuterRefl_shift (n : Ω → ℤ)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hX : ∀ ω ∈ A, R5Wall.outerExc R L r η ψ q ω ⊆ X ω) :
    R5Lift.R7OuterRefl P A R L r η ψ xL xR
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' ζ' X q := by
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    ((hcfg ω hω).conf.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos (hcfg ω hω).conf
      (hcfg ω hω).bounded)).isOpen
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hcfg ω hω).conf.changePocket_subset_H
  have hf := shiftChart_dom_facts (A := A) (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ) hCo hCH
    (fun ω hω => (hψ ω hω).2.2.2.1) n
  exact r7OuterRefl_of_cfg hcfg hψ (fun ω hω => (hf ω hω).1) (fun ω hω => (hf ω hω).2.1)
    (fun ω hω => (hf ω hω).2.2) hX

/-- **`R5Lift.R7OuterReflInf` for the shifted pocket chart** (seed-opening reverse-contained pocket). -/
theorem r7OuterReflInf_shift (n : Ω → ℤ)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hX : ∀ ω ∈ A, R5Wall.outerExcInf R L r η ψ q ω ⊆ X ω) :
    R5Lift.R7OuterReflInf P A R L r η ψ xL xR
      (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) W' ζ' X q := by
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    ((hcfg ω hω).conf.isCfPocketInf (hcfg ω hω).seed).isOpen
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    ((hcfg ω hω).conf.isCfPocketInf (hcfg ω hω).seed).subset_H
  have hf := shiftChart_dom_facts (A := A) (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ) hCo hCH
    (fun ω hω => (hψ ω hω).2.2.2.1) n
  exact r7OuterReflInf_of_cfg hcfg hψ (fun ω hω => (hf ω hω).1) (fun ω hω => (hf ω hω).2.1)
    (fun ω hω => (hf ω hω).2.2) hX

end InteractingSLE.Sec7.WallOrd
