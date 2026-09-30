import QuantumZipper.Proofs.Zipper.F2Step3DensCore
import QuantumZipper.Proofs.Zipper.RegUnif

/-!
# F2 step (3): `Step3LocalDensityStmt` from its four ingredients

Theorem 1.3, node F2, step (3), input `Step3LocalDensityStmt` (`F2Step3.lean`), following
Sheffield, arXiv:1012.4797, §5.1, pp. 60–62 (rule (5.1): adding a function continuous near a
boundary interval multiplies the boundary measure there by `e^{γφ/2}`; Duplantier–Sheffield,
*LQG and KPZ*, (5.1)). With `W = √κ B`, `a = O⁻_t`, `b = O⁺_t`, `x_t`, `y_t` the unzipped fields
of `x = X + α₀(−log|·|)` and `y = x + γ log|·| = h⁰ + X`, and `E_t = extInv W t` (`f_t⁻¹` on `ℍ`,
its boundary extension `F_t = invBdry W t` on `ℝ`):

* (i) **Carathéodory** (`Step3BdryExtStmt`): `E_t` is continuous and nonvanishing on `V ∩ ℍ̄` for
  an open `V ⊇ (a, b)` (Pommerenke, *Boundary Behaviour of Conformal Maps*, 1992, Thm 2.6, for
  the reverse map `fwdMapInv = revMap ∘ timeRev`; `η(0,t]` is a simple arc not through `0`);
* (ii) **field identity** (`Step3FieldIdStmt`): near `(a, b)`, `x_t = y_t − γ log|E_t|` at the
  level of `avgReg` (`coordChange` is affine in the field; the `ofFun` part `γ log|·|` transforms
  by composition with `f_t⁻¹`);
* (iii) rule (5.1) (`restrict_eq_logDens`, proved) for the regular sample `y_t`
  (`Step3RegStmt`, proved from `RegUnif.JointModStmt` in `step3Reg_of_jointMod`), with the
  global vague limits existing (`Step3ExistStmt`);
* (iv) the endpoint facts: `a ≤ 0 ≤ b` (`Step3SideSignStmt`) and no atoms at `a`, `b`
  (`Step3NoAtomStmt`).

The assembly `step3LocalDensity_of_inputs` is our own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- `f_t⁻¹` on `ℍ`, and its boundary extension `F_t = invBdry W t` on `ℝ` (and below). -/
def extInv (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  if 0 < z.im then fwdMapInv W t z else invBdry W t z.re

@[simp] theorem extInv_ofReal (W : ℝ → ℝ) (t s : ℝ) : extInv W t (s : ℂ) = invBdry W t s := by
  simp [extInv]

/-- The unzipped `x_t` of `x = X + α₀(−log|·|)`. -/
def unzX (κ : ℝ) (X : FieldSample) (W : ℝ → ℝ) (t : ℝ) : FieldSample :=
  unzippedField (Real.sqrt κ) (X + logSingField κ, W) t

/-- The unzipped `y_t` of `y = x + γ log|·|`. -/
def unzY (κ : ℝ) (X : FieldSample) (W : ℝ → ℝ) (t : ℝ) : FieldSample :=
  unzippedField (Real.sqrt κ) ((X + logSingField κ) + gammaLog κ, W) t

/-- **Input (iv-a).** a.s., for all `t ≥ 0`, `O⁻_t ≤ 0 ≤ O⁺_t`. -/
def Step3SideSignStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (sideImages (drive κ B ω) t).1 ≤ 0 ∧ 0 ≤ (sideImages (drive κ B ω) t).2

/-- **Input (i), Carathéodory.** a.s., for all `t ≥ 0`, there is an open `V ⊇ (O⁻_t, O⁺_t)` on
whose trace on `ℍ̄` the map `E_t` (`f_t⁻¹` in `ℍ`, `F_t` on `ℝ`) is continuous and nonvanishing. -/
def Step3BdryExtStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∃ V : Set ℂ, IsOpen V ∧
      (∀ s ∈ Ioo (sideImages (drive κ B ω) t).1 (sideImages (drive κ B ω) t).2, (s : ℂ) ∈ V) ∧
      ContinuousOn (extInv (drive κ B ω) t) (V ∩ Hbar) ∧
      ∀ z ∈ V ∩ Hbar, extInv (drive κ B ω) t z ≠ 0

end F2
end QuantumZipper
