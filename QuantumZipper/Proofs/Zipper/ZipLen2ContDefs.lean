import QuantumZipper.Proofs.Zipper.XFlowClose

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2 continuum: definitions

The `Γ⁰` pairings of the flow node at a **continuous** smoothing radius `ρ > 0`:

`Φ^c(p, ρ) = ∫ evalReg y_u (fc(z, ρ)) dν_p(z)`, `y = 𝔥₀ + x`, `ν_p = (R_{u,s})_* fc(d, r)`,

and the matching deterministic part `det^c(p, ρ) = ∫∫ Ψ_u dfc(z, ρ) dν_p(z)` (the continuous-radius
versions of `F1.flowPhiY`, `F1.flowDetJ`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

/-- The `Γ⁰` pairing at continuous smoothing radius `ρ`. -/
def flowPhiYc (κ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (ρ : ℝ) (p : ℝ × ℝ × ℂ × ℝ) : ℝ :=
  ∫ z, evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) p.1) (foldedCircle z ρ)
    ∂F1.flowNu W p

/-- The deterministic part at continuous smoothing radius `ρ`. -/
def flowDetC (κ : ℝ) (W : ℝ → ℝ) (p : ℝ × ℝ × ℂ × ℝ) (ρ : ℝ) : ℝ :=
  ∫ z, (∫ v, RegUnif.PsiU κ W p.1 v ∂foldedCircle z ρ) ∂F1.flowNu W p

/-- **(Fixed-driver continuous-radius Cauchy property.)** For a Hölder driver on `[0, 2m+2]`,
a.s. in the field, the pairings `Φ^c(q, ρ)` are Cauchy as `ρ → 0⁺` along rational radii,
uniformly over the rational points `q` of `flowBox m`. -/
def FlowFixedUCcStmt (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → FieldSample) : Prop :=
  ∀ m : ℕ, ∀ W : ℝ → ℝ, ∀ a CH : ℝ, RegUnif.HolderDrv W (2 * (m : ℝ) + 2) a CH →
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ N : ℕ, ∀ ρ ρ' : ℚ, 0 < ρ → (ρ : ℝ) ≤ 1 / ((N : ℝ) + 1) →
      0 < ρ' → (ρ' : ℝ) ≤ 1 / ((N : ℝ) + 1) →
      ∀ q : ℚ × ℚ × ℚ × ℚ × ℚ, F1.flowQ q ∈ F1.flowBox m →
        |flowPhiYc κ (X ω) W ρ (F1.flowQ q) - flowPhiYc κ (X ω) W ρ' (F1.flowQ q)| ≤
          1 / ((n : ℝ) + 1)

/-- The same Cauchy property along the Brownian driver `W = √κ B`. -/
def FlowBrownUCcStmt (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ N : ℕ, ∀ ρ ρ' : ℚ, 0 < ρ → (ρ : ℝ) ≤ 1 / ((N : ℝ) + 1) →
      0 < ρ' → (ρ' : ℝ) ≤ 1 / ((N : ℝ) + 1) →
      ∀ q : ℚ × ℚ × ℚ × ℚ × ℚ, F1.flowQ q ∈ F1.flowBox m →
        |flowPhiYc κ (X ω) (drive κ B ω) ρ (F1.flowQ q) -
          flowPhiYc κ (X ω) (drive κ B ω) ρ' (F1.flowQ q)| ≤ 1 / ((n : ℝ) + 1)

end ZipLen
end B3d
end QuantumZipper
