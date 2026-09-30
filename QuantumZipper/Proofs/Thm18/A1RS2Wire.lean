import QuantumZipper.Proofs.Thm18.A1RS2Y2
import QuantumZipper.Proofs.Thm18.A1RS2Y3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (10): `A1RFSmearContStmt` from the rational Cauchy estimate

The continuity inputs of the extension `tendsto_of_ratCauchy` are proved for the Theorem 1.8
field: (R2) `ae_continuousOn_smearFam_pos` (A1RS2Y2.lean) and (R3)
`ae_continuousOn_smearFam_zero` (A1RS2Y3.lean). What remains of `A1RFSmearContStmt` is the
countable estimate `A1RSRatCauchyStmt`: a.s., on every rational box of `smearU`, the pairings at
rational radii `r → 0⁺` approach the member at `r = 0` uniformly over the rational parameters.
This is the random-driver form of the proved fixed-driver free-field estimate
`ae_smear_cauchy_fixed` (Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1); passing to it
needs the transfer to the Brownian driver, the wedge profile `α₀(−log|·|) + G` and the rescaling
by the canonical scale (see the file docstrings of A1RS2Fix and A1RS2Prof).

**`a1rfSmearContStmt_of_ratCauchy : A1RSRatCauchyStmt → A1RFSmearContStmt`.** Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- **The rational Cauchy estimate for the Theorem 1.8 field** (open). -/
def A1RSRatCauchyStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ᵐ ω ∂P,
      ∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
        (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
          |evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left (ratPt q) r) -
            evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left (ratPt q) 0)| < 1 / ((n : ℝ) + 1)

/-- **`A1RFSmearContStmt` from the rational Cauchy estimate.** -/
theorem a1rfSmearContStmt_of_ratCauchy (h : A1RSRatCauchyStmt) : A1RFSmearContStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  filter_upwards [h γ P B Y hS hIn left, ae_continuousOn_smearFam_pos γ P B Y hS hIn left,
    ae_continuousOn_smearFam_zero γ P B Y hS hIn left] with ω hC h2 h3 t ht d _ s hs
  set p : Fin 4 → ℝ := ![t, d.re, d.im, s] with hpdef
  have hp0 : p 0 = t := rfl
  have hp3 : p 3 = s := rfl
  have hp : p ∈ smearU := ⟨by rw [hp0]; exact ht, by rw [hp3]; exact hs⟩
  have hpd : parD p = d := Complex.ext rfl rfl
  have key := tendsto_of_ratCauchy
    (Φ := fun ρ p => evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left p ρ))
    (E0 := fun p => evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left p 0)) hC h2 h3 p hp
  have e : ∀ ρ : ℝ, smearFam (drive (γ ^ 2) B ω) left p ρ =
      a1rfNu (drive (γ ^ 2) B ω) t left d s ρ := fun ρ => by
    simp only [smearFam, hp0, hp3, hpd]
  simp only [e] at key
  exact key

end A1RS
end R18
end QuantumZipper
