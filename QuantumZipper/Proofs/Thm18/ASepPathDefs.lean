import QuantumZipper.Proofs.Thm18.ASepD84

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP: the per-path form of the `τ' = 0` A-sep leaf

`G4SepRep0Stmt` (ASepD84.lean) asks for a measurable set `E` of (path, wedge data) pairs, all good,
charged by the product law. It splits into

* the **per-path statement** `G4SepPath0Stmt`: for every fixed driver `W` with the regularity of a
  Brownian SLE driver (`DrvGood`: continuous, `W 0 = 0`, Hölder on every `[0, T]`, real points
  alive), almost surely in the wedge sample the `τ' = 0` exactness conclusion holds;
* the **transfer** `G4SepPath0Stmt → G4SepRep0Stmt` (measurability of `E`, a.s. `DrvGood` of the
  Brownian driver: `RS.bm_holder`, `RS.ae_real_alive`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- Regularity of a driver used by the A-sep engine. -/
def DrvGood (W : ℝ → ℝ) : Prop :=
  Continuous W ∧ W 0 = 0 ∧
    (∀ T : ℝ, 0 < T → ∃ α CH : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ CH ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
        |W t - W t'| ≤ CH * |t - t'| ^ α) ∧
    (∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol W (x : ℂ) T v)

/-- **Per-path A-sep at `τ' = 0`.** -/
def G4SepPath0Stmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      ∀ W : ℝ → ℝ, DrvGood W → ∀ᵐ ω' ∂P', G4SepConcl0 γ (wedgeRep γ X A ω', W)

end ASep
end QuantumZipper
