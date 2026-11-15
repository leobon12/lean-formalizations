/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J5ChartClauseFour
import InteractingSLE.WangWu.J7CondMain

/-!
# (J5) in the form of WW-B23's `ChamberCond.ChamberClauseStatement`

Packet PROVE-WW-B22. PROVE-WW-B23 assembled `Chamber4.Chamber4JointStatement` from Proposition 4.19, Lemma 4.21 and the
**fixed-time** chamber clause `ChamberCond.ChamberClauseStatement` (every seed three-line space carries a chamber
construction, a wall-measurable lift shift and the chart coupling clause of the seed word at every deterministic
capacity time, on the event that the time is below the terminal capacity). This file derives that statement from the
one remaining input of (J5) at `κ = 4`, the side limits of the active chamber component along the middle line:

* `ChamberCurveSideStatement` (**named input**, (CS) at `κ = 4`): on every seed three-line space, for every chamber
  construction with capacity data, at every capacity time, almost surely below the terminal capacity, every harmonic
  representative of the mean of the three complete lines has the side limits `Sec7.Lemma71N.PocketCurveSide` at the
  chart points of the two middle intervals (chart `shiftLift c 0`, mean `pocketGl 4 …`);
* **`chamberClauseStatement_of_curveSide`**: `ChamberCurveSideStatement → ChamberCond.ChamberClauseStatement`, with the
  chamber construction `exists_isPocketConstruction_three`, the capacity data `exists_capData_three`, lift shift `0`,
  `a = 0`, `k = χ(4)`, and the clause `isChartCouplingCharFunConst_four_of_curveSide` (the wall side limits are proved).

Conditional helper (on the middle-line side limits); it replaces no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedThree

open Sec7 MartChar Sec7.Lemma71C Sec7.Lemma71D Sec7.Lemma71E Sec7.Lemma71K Sec7.Lemma71L Sec7.Lemma71M Sec7.Lemma71N
  Sec6 LocalSets

/-- **Named input ((CS) at `κ = 4`): the side limits of the active chamber component along the middle line.** On every
seed three-line space, for every chamber construction with its capacity data, at every capacity time `t` and for every
version `gL` of the local-set mean of the three complete lines: almost surely on `{t < capLife}`, for every harmonic
representative `vL` of `gL`, at every chart point `x` of `(L_t − W_t, 0) ∪ (0, R_t − W_t)` the inverse chart of the
remaining chamber lands at a point `p` of the stopped union `A(τ_t)` (or of `ℝ`) near which the full union lies in
`A(τ_t)`, and `vL + u₀ − G_t → 0` at `x` (`Sec7.Lemma71N.PocketCurveSide`; Proposition 4.20 on the middle line). -/
def ChamberCurveSideStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (rL rR u₁ u₂ : ℝ)
    (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ),
    IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ →
    ∀ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ), IsPocketConstruction P β α γ C c γ' →
    ∀ (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ),
      Measurable G → MeasurableSet M → Measurable Y → (∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) →
      (∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z) → (∀ ω, Y (outerHist β α ω) = closePt α C ω) →
    ∀ (t : ℝ≥0) (gL : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        PocketCurveSide (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) vL u₀
          (pocketInv (shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s) t)
          (pocketGl 4 (fun _ : Fin 1 => u₂ / wwLambda - 2) (fun _ : Fin 1 => -u₁ / wwLambda - 2)
            (shiftLift (c ω) 0) (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t 0)
          (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t)
          (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t)

/-- **WW-B23's fixed-time chamber clause from the middle-line side limits** (`ChamberCond.ChamberClauseStatement`):
on every seed three-line space, the chamber construction of `exists_isPocketConstruction_three` with lift shift `0`,
`a = 0`, `k = χ(4)` satisfies the chart coupling clause of the seed word `(u₂/λ − 2; −u₁/λ − 2)` at every deterministic
capacity time on `{t < capLife}` (`isChartCouplingCharFunConst_four_of_curveSide`). Conditional helper. -/
theorem chamberClauseStatement_of_curveSide (hcs : ChamberCurveSideStatement.{u}) :
    ChamberCond.ChamberClauseStatement.{u} := by
  intro Ω mΩ P hP rL rR u₁ u₂ h u₀ β α γ hS
  have hT : IsThreeLineSpace P h u₀ β α γ := hS.2.2.2.2.2.2.1
  obtain ⟨C, c, γ', hpc⟩ := exists_isPocketConstruction_three hT
  obtain ⟨G, M, Y, hG, hM, hY, hMiff, hGeq, hYeq⟩ := exists_capData_three hT hpc
  exact ⟨C, c, γ', fun _ => 0, 0, chiC 4, hpc, measurable_const,
    isChartCouplingCharFunConst_four_of_curveSide hS hpc hG hM hY hMiff hGeq hYeq
      (hcs P rL rR u₁ u₂ h u₀ β α γ hS C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq)⟩

end InteractingSLE.WangWu.SeedThree
