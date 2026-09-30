import QuantumZipper.Proofs.Zipper.E5ESM5
import QuantumZipper.Proofs.Zipper.E5PalmRepr
import QuantumZipper.Proofs.Zipper.E5Main5

/-!
# E5-ESM, part 6: E5's left side on the level model space `(ℝ≥0 × Ω̄) × Ω'`

Task E5-G0ESM (Theorem 1.3, node E5; blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E5 steps (1)
and (3); `handoff/E5.md` items 1 and 4; Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, proof of
Lemma 5.6).

Combines the Palm representation of E5-PALM (`palm_repr_iter`: E4 replaces the collided field by
the collision target field of an independent free field `X'`, given the readability input
`PalmReadable`) with the E-SM(b) Bayes structure (`palm_level_bayes`): on the model space
`Ω₁ = (ℝ≥0 × Ω̄) × Ω'` with `Q₁ = (𝐑.withDensity w) ⊗ P' = (𝐑 ⊗ P').withDensity (w ∘ fst)`,

`lhs C Γ = p · E_{Q₁} Γ(loc R (zcfgTL C))`,

`zcfgTL C ((ℓ, ω), ω') = canon(targetColl(V^ω, τ_{x(ℓ)}, ϖ, X'(ω')) + C/γ, drvMap κ (D(ℓ, ω)))`
with `D = esmGerm` the Brownian germ at the level time. Together with `E5ESM3.esm_germ_fields`
(the germ is Brownian on `[0, u₀]` and independent of `(𝒢, X', D^{+u₀})` under `𝐑 ⊗ P'`) this is
the model-space side of `E5ReprG` for the fields `Ω₁, Q, Rr, w, hw1, hQ, D, hD, hDc, hind, hDW`.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2 E1 CoordsFull E4Grid

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

/-- The model configuration with a given driver `d` (`zcfgT` with the collided driver replaced). -/
def zcfgTd (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (ϖ : Measure ℂ) (X' : Ω' → FieldSample) (C : ℝ) (ω : Ω)
    (x : ℝ) (ω' : Ω') (d : ℝ → ℝ) : FieldSample × (ℝ → ℝ) :=
  canonConfig (Real.sqrt κ) (addConst (targetColl κ (Vr κ T B ω) (palmTau κ T B ω x) ϖ (X' ω'))
    (C / Real.sqrt κ), d)

/-- **The level model configuration**: at `((ℓ, ω), ω')`, the collision target field of `X'(ω')`
at the Palm point `x(ℓ)`, shifted by `C/γ`, with driver `√κ ×` the germ `D(ℓ, ω)`,
canonicalized. -/
def zcfgTL (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω) (ϖ : Measure ℂ)
    (X' : Ω' → FieldSample) (C : ℝ) (z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω') :
    FieldSample × (ℝ → ℝ) :=
  zcfgTd κ T B ϖ X' C (ofCompl P z.1.2) (xL κ T B X z.1.1 (ofCompl P z.1.2)) z.2
    (drvMap κ (esmGerm κ T B X P z.1))

/-- The Palm test of the model side at level `C`. -/
def palmTestT {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ϖ : Measure ℂ) (P' : Measure Ω') (X' : Ω' → FieldSample) (R : ℕ) (C : ℝ)
    (Γ : L → ℝ≥0∞) : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞ :=
  fun ω x c => ∫⁻ ω', Γ (loc R (zcfgTd κ T B ϖ X' C ω x ω' c.2)) ∂P'

omit [IsProbabilityMeasure P] [IsProbabilityMeasure P'] in
lemma lvlG_palmTestT {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (R : ℕ) (C : ℝ)
    (Γ : L → ℝ≥0∞) (p : ℝ≥0 × NullMeasurableSpace Ω P) :
    lvlG κ T B X (palmTestT loc κ T B ϖ P' X' R C Γ) p.1 (ofCompl P p.2) =
      ∫⁻ ω', Γ (loc R (zcfgTL κ T B X P ϖ X' C (p, ω'))) ∂P' := by
  simp only [lvlG, palmTestT, zcfgTL]
  rw [zipCapDown_cfg_snd κ B X (levelTime (lenA κ T B X) T.toNNReal p.1) (ofCompl P p.2)]
  rfl

/-- **E5's left side on the level model space.** Given E5's setup with pathwise continuous `B`,
an independent free field `X'`, `δ > 0`, the readability input at every level `C`, positive finite
masses and measurability of the Palm density, there is one density `w` with `∫ w d𝐑 = 1` such
that for every level `C` and measurable test `Γ` whose model integrand is jointly measurable,
`lhs C Γ = p · ∫ Γ(loc R (zcfgTL C)) d((𝐑.withDensity w) ⊗ P')`. -/
theorem lhsF_eq_levelModel {L : Type*} [MeasurableSpace L]
    (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (hS : E5.Setup κ T P B X ϖ)
    (hX' : IsFreeGFFModConstH X' P') (hBc : ∀ ω, Continuous (B · ω)) {δ : ℝ} (hδ : 0 < δ)
    (R : ℕ) {Rd : ℝ → CfgE × (ℕ → ℝ) → L}
    (hRd : ∀ C, PalmReadable loc κ T P B X ϖ P' X' δ R C (Rd C))
    (hpos : esmMeas κ T B X P lvlMu univ ≠ 0) (hfin : esmMeas κ T B X P lvlMu univ ≠ ⊤)
    (hp0 : pmass κ T P B X ϖ δ ≠ 0)
    (hw0 : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      w0 κ T B X ϖ δ z.1 (ofCompl P z.2)) :
    ∃ w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞, Measurable w ∧
      ∫⁻ z, w z ∂esmRr κ T B X P lvlMu = 1 ∧
      ∀ (C : ℝ) (Γ : L → ℝ≥0∞), Measurable Γ →
        (Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
          Γ (loc R (zcfgTL κ T B X P ϖ X' C z))) →
        lhsF loc κ T P B X ϖ δ R C Γ = pmass κ T P B X ϖ δ *
          ∫⁻ z, Γ (loc R (zcfgTL κ T B X P ϖ X' C z))
            ∂((esmRr κ T B X P lvlMu).withDensity w).prod P' := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := id hS
  obtain ⟨w, hw, hw1, hG⟩ := palm_level_bayes hκ hκ4 hT hB hX hind hBc ϖ δ hpos hfin hp0
    (pmass_ne_top hS hδ) hw0
  refine ⟨w, hw, hw1, fun C Γ hΓ hJ => ?_⟩
  have hLG : Measurable fun p : ℝ≥0 × NullMeasurableSpace Ω P =>
      lvlG κ T B X (palmTestT loc κ T B ϖ P' X' R C Γ) p.1 (ofCompl P p.2) := by
    simp only [lvlG_palmTestT]
    exact hJ.lintegral_prod_right'
  have hFm : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      lvlF κ T B X ϖ δ (palmTestT loc κ T B ϖ P' X' R C Γ) z.1 (ofCompl P z.2) := by
    simp only [lvlF_eq_w0_mul]
    exact hw0.mul hLG
  have h1 : lhsF loc κ T P B X ϖ δ R C Γ =
      palmInt κ T P B X ϖ δ (palmTestT loc κ T B ϖ P' X' R C Γ) :=
    palm_repr_iter loc hS hX' hδ R C (hRd C) Γ hΓ
  rw [h1, hG _ hFm, lintegral_prod _ hJ.aemeasurable]
  simp only [lvlG_palmTestT]

end E5
end QuantumZipper
