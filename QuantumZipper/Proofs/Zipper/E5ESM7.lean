import QuantumZipper.Proofs.Zipper.E5ESM6
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# E5-ESM, part 7: the E-SM(b) model package for `E5.ZoomModel`

Task E5-G0ESM (Theorem 1.3, node E5; blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E-SM(b), E5
steps (1), (3); Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, proof of Lemma 5.6).

`e5_esm_model`: on `Ω₁ = (ℝ≥0 × Ω̄) × Ω'` there are a probability measure `Rr₁ = 𝐑 ⊗ P'` and a
measurable density `w₁` with `∫ w₁ dRr₁ = 1` such that, with `Q₁ = Rr₁.withDensity w₁`:

* (Palm representation, E5 step (1) + E-SM(b)) `lhs C Γ = p · E_{Q₁} Γ(loc R (zcfgTL C))` for every
  level `C` and test `Γ` with jointly measurable model integrand;
* (germ, E5 step (3)) the germ `D = esmGerm ∘ fst` is measurable with continuous paths,
  `Rr₁.map (pathRestr u₀ ∘ D) = W.map (pathRestr u₀)`, and `pathRestr u₀ ∘ D` is independent under
  `Rr₁` of `Φ((V, ω'), D^{+u₀})` for every measurable `Φ` and every `V` that is
  `𝓕_{T_ℓ}`-measurable level by level;
* the driver of `zcfgTL C` is `drvMap κ D` (definitional).

The positivity and finiteness of the level mass are proved here (`lvlMu` is finite; the level mass
vanishing would force `p = 0`). Remaining inputs are explicit: `hBc`, `PalmReadable` (E5-PALM2),
`p ≠ 0`, measurability of the Palm density `w0` and of the model integrands. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 CoordsFull E4Grid

instance isFiniteMeasure_lvlMu : IsFiniteMeasure lvlMu := by
  refine ⟨?_⟩
  rw [lvlMu, Measure.map_apply measurable_real_toNNReal MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (integrableOn_exp_neg_Ioi 0).lintegral_lt_top

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

lemma esmMeas_lvlMu_ne_top : esmMeas κ T B X P lvlMu univ ≠ ⊤ :=
  ne_top_of_le_ne_top (measure_ne_top (lvlMu.prod P.completion) univ)
    (Measure.restrict_apply_le _ _)

/-- A positive Palm mass forces a positive level mass. -/
lemma esmMeas_lvlMu_ne_zero (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (δ : ℝ) (hp0 : pmass κ T P B X ϖ δ ≠ 0)
    (hw0 : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      w0 κ T B X ϖ δ z.1 (ofCompl P z.2)) :
    esmMeas κ T B X P lvlMu univ ≠ 0 := by
  intro h
  have h0 : esmMeas κ T B X P lvlMu = 0 := Measure.measure_univ_eq_zero.1 h
  have hL : palmInt κ T P B X ϖ δ (fun _ _ _ => 1) = ∫⁻ z, w0 κ T B X ϖ δ z.1 (ofCompl P z.2)
      ∂esmMeas κ T B X P lvlMu := palm_eq_level hκ hκ4 hT hB hX hind hBc ϖ δ _ hw0
  rw [palmInt_one hκ hκ4 hT hB, h0, lintegral_zero_measure] at hL
  exact hp0 hL

end E5
end QuantumZipper
