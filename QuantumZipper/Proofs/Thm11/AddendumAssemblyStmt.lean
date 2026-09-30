import QuantumZipper.Statements.Thm11
import QuantumZipper.Proofs.GFF.K3.C5Kernel

/-!
# Theorem 1.1 addendum, AD-8: the not-yet-proved input nodes as explicit propositions

Blueprint `blueprint/THM11_BLUEPRINT.md` §9 (AD-4, AD-8).  (K3 node C5 is proved:
`K3.zeroGFFTestCov_sleComplement`, used directly by the assembly; `V_T = K3.VT`.)  Sheffield, *Conformal weldings of random surfaces*
(arXiv:1012.4797), Theorem 1.1 and its addendum for `κ ∈ (4,8)` (p. 12).

These are hypotheses of the assembly `Thm11Asm.theorem1_1_addendum_of_nodes`; each is stated
exactly as it is consumed there.

* `ExtIntStmt` — part of AD-4: `ρ · 𝔥^ext_T` is a.s. integrable.
* `ExtMartStmt` — AD-4 + MF-5 (the addendum analogue of the proved `MainMart.main_mart`):
  `E exp(i(𝔥^ext_T, ρ) − ½ ∬ρρ V_T) = exp(i(𝔥₀, ρ) − ½ ∬ρρ G_ℍ)`.
* `ExtMeasStmt` — joint measurability of `(ω, z) ↦ 𝔥^ext_T(z)` for driving paths that are
  measurable in `ω` and continuous in `t` (the addendum analogue of the proved
  `CharFunRhs.measurable_hTmF`); it is what makes `(𝔥^ext_T, ρ)` a measurable function of
  `pathOf B`, as AD-8 requires (`F = cos, sin` of it).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal

namespace QuantumZipper
namespace Thm11Asm

/-- **AD-4, integrability part.** `ρ · 𝔥^ext_T` is almost surely integrable. -/
def ExtIntStmt : Prop :=
  ∀ κ T : ℝ, 4 < κ → κ < 8 → 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
    IsBrownianReal B P → ∀ ρ : TestFun H,
    ∀ᵐ ω ∂P, Integrable fun z => ρ.1 z * hTfwdExt κ (drive κ B ω) T z

/-- **AD-4 + MF-5** (addendum analogue of `MainMart.main_mart`): the limit `δ → 0` of the
frozen-field martingale identity, with limits `(𝔥^ext_T, ρ)` and `∬ ρρ V_T`. -/
def ExtMartStmt : Prop :=
  ∀ κ T : ℝ, 4 < κ → κ < 8 → 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
    IsBrownianReal B P → ∀ ρ : TestFun H,
    ∫ ω, cexp (I * ((∫ z, ρ.1 z * hTfwdExt κ (drive κ B ω) T z : ℝ) : ℂ) -
        ((∫ a, ∫ b, ρ.1 a * ρ.1 b * K3.VT (drive κ B ω) T a b : ℝ) : ℂ) / 2) ∂P =
      cexp (I * ((∫ z, ρ.1 z * h0fwd κ z : ℝ) : ℂ) -
        ((∫ x, ∫ y, ρ.1 x * ρ.1 y * greenH x y : ℝ) : ℂ) / 2)

/-- **Measurability of the extended field** (implicit in AD-8): for driving paths measurable in
`ω` and continuous in `t`, `(ω, z) ↦ 𝔥^ext_T(z)` is jointly measurable. -/
def ExtMeasStmt : Prop :=
  ∀ κ T : ℝ, 4 < κ → κ < 8 → 0 < T →
  ∀ {Ω : Type} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ),
    (∀ t, Measurable (B t)) → (∀ ω, Continuous fun t => B t ω) →
    Measurable fun p : Ω × ℂ => hTfwdExt κ (drive κ B p.1) T p.2

end Thm11Asm
end QuantumZipper
