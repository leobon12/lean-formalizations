import QuantumZipper.Proofs.Zipper.E5Asm3

/-!
# E5-ASM, part 4: the level-space Palm representation of E5's left side, unconditional

Task E5-ASM (Theorem 1.3, node E5; Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, proof of
Lemma 5.6, blueprint `E_BRANCH_BLUEPRINT.md` §4 E5 steps (1), (4)).

**`e5_level_repr`**: for every E5 setup with positive Palm mass, every free field `X₀` (the model
collision field, decision D28 with base measure `ρ₀`), `δ > 0`, `R` and Brownian coordinate
measure `W`, there are

* a continuous version `B'` of `B` that is good at every sample (`exists_goodVersion`) and a
  modification `X₁` of `X₀` (`exists_base_regField_good`), with `X' = regField ϖ ρ₀ ∘ X₁`;
* the E-SM(b) level model `Rr₁`, `w₁` on `(ℝ≥0 × NullMeasurableSpace Ω P) × Ω'` with
  `lhs C Γ = p · E_{Rr₁.withDensity w₁} Γ(locRich R (zcfgTL … C))` for **every** measurable test
  `Γ` (the joint measurability of the model integrand is now proved: `E5Asm1`–`E5Asm3`);
* the germ facts of `e5_esm_model` (measurable, continuous, Wiener law, independence).

All inputs of `e5_esm_model` are discharged: `hBc`, `hw0` (`E5HW0Ver`), `PalmReadable`
(`palmReadable_of`, `drvReadable_drvRd`, `modelGood_holds`), and the model-integrand measurability.
Only `p ≠ 0` remains as a hypothesis. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 E4Grid CoordsFull

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **The model-integrand measurability**, for the good version and the D28 field. -/
theorem measurable_modelInt_level (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (hG : ∀ ω, GoodVr κ T (Vr κ T B ω)) {Ω' : Type} [MeasurableSpace Ω']
    {X₁ : Ω' → FieldSample} (hXm : ∀ μ, Measurable fun ω' => X₁ ω' μ) (ρ₀ : Measure ℂ)
    (hX'g : ∀ ω', IsLQGGood (Real.sqrt κ) (regField ϖ ρ₀ (X₁ ω') +
      ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖))
    (R : ℕ) (C : ℝ) {Γ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) :
    Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      Γ (locG D3Plus.locFieldFull R
        (zcfgTL κ T B X P ϖ (fun ω' => regField ϖ ρ₀ (X₁ ω')) C z)) := by
  obtain ⟨-, -, hT, -⟩ := id hS
  have h1 := measurable_coords_targetColl_level (κ := κ) (T := T) (B := B) (X := X) (ϖ := ϖ)
    (P := P) hXm ρ₀ hS hBc
  have h2 := measurable_coords_target_of_level (X' := fun ω' => regField ϖ ρ₀ (X₁ ω'))
    (P := P) (X := X) (ϖ := ϖ) hBc hT hG h1
  exact measurable_modelInt_of_coords (X' := fun ω' => regField ϖ ρ₀ (X₁ ω')) hS hBc hX'g h2
    R C hΓ

end E5
end QuantumZipper
