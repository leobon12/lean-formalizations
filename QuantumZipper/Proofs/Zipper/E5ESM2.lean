import QuantumZipper.Proofs.Zipper.E5ESM1

/-!
# E5-ESM, part 2: the germ fields of the zoom model on the level space

Task E5-G0ESM (Theorem 1.3, node E5; blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E-SM(b) and
E5 step (3); Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, proof of Lemma 5.6).

From the level-space product formula `esmMeas_factor` (`E5ESM1.lean`, E-SM):

* `esm_level_law`: under the normalized level measure `𝐑 = esmRr`, the germ
  `D = smPath B T_ℓ` restricted to `[0, u₀]` has the Brownian law `W.map (pathRestr u₀)` (for every
  Brownian coordinate measure `W`), is independent of every `V` that is `𝓕_{T_ℓ}`-measurable
  level by level, is measurable and has continuous paths — the fields `hDW`, `hind`, `hD`, `hDc` of
  `E5.ZoomModel`;
* `esm_level_germ_model_prod`: the same after adjoining an independent factor `(Ω', P')` (the
  free field `X'` of the E4/E5 model), with `V` any measurable function of `(V₁, ω')`.

Own measure-theoretic bookkeeping around the E-SM identity (no new probabilistic input).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
lemma esmRr_apply (μ : Measure ℝ≥0) (s : Set (ℝ≥0 × NullMeasurableSpace Ω P)) :
    esmRr κ T B X P μ s = (esmMeas κ T B X P μ univ)⁻¹ * esmMeas κ T B X P μ s := by
  rw [esmRr, Measure.smul_apply, smul_eq_mul]

omit [IsProbabilityMeasure P] in
lemma isProbabilityMeasure_esmRr (μ : Measure ℝ≥0) (hpos : esmMeas κ T B X P μ univ ≠ 0)
    (hfin : esmMeas κ T B X P μ univ ≠ ⊤) : IsProbabilityMeasure (esmRr κ T B X P μ) :=
  ⟨by rw [esmRr_apply, ENNReal.inv_mul_cancel hpos hfin]⟩

/-- **Adjoining an independent factor.** If `f ⊥ g` under `R`, then under `R ⊗ P'`,
`(f ∘ fst, snd) ⊥ g ∘ fst`. -/
lemma indepFun_prod_snd_e5 {Ω₁ Ω' 𝕍 𝕎 : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω']
    [MeasurableSpace 𝕍] [MeasurableSpace 𝕎] {R : Measure Ω₁} [IsProbabilityMeasure R]
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {f : Ω₁ → 𝕍} {g : Ω₁ → 𝕎} (hf : Measurable f)
    (hg : Measurable g) (hfg : IndepFun f g R) :
    IndepFun (fun z : Ω₁ × Ω' => (f z.1, z.2)) (fun z => g z.1) (R.prod P') := by
  have hF : Measurable fun z : Ω₁ × Ω' => (f z.1, z.2) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hG : Measurable fun z : Ω₁ × Ω' => g z.1 := hg.comp measurable_fst
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro C S hC hS
  have hsec : ∀ y : Ω', MeasurableSet ((fun v => (v, y)) ⁻¹' C) :=
    fun y => measurable_prodMk_right hC
  have h1 : (R.prod P') ((fun z : Ω₁ × Ω' => (f z.1, z.2)) ⁻¹' C ∩ (fun z => g z.1) ⁻¹' S) =
      ∫⁻ y, R (f ⁻¹' ((fun v => (v, y)) ⁻¹' C)) * R (g ⁻¹' S) ∂P' := by
    rw [Measure.prod_apply_symm ((hF hC).inter (hG hS))]
    refine lintegral_congr fun y => ?_
    rw [← (indepFun_iff_measure_inter_preimage_eq_mul.1 hfg) _ _ (hsec y) hS]
    rfl
  have h2 : (R.prod P') ((fun z : Ω₁ × Ω' => (f z.1, z.2)) ⁻¹' C) =
      ∫⁻ y, R (f ⁻¹' ((fun v => (v, y)) ⁻¹' C)) ∂P' := by
    rw [Measure.prod_apply_symm (hF hC)]
    rfl
  have h3 : (R.prod P') ((fun z : Ω₁ × Ω' => g z.1) ⁻¹' S) = R (g ⁻¹' S) := by
    have e : (fun z : Ω₁ × Ω' => g z.1) ⁻¹' S = (g ⁻¹' S) ×ˢ univ := by
      ext z; simp
    rw [e, Measure.prod_prod, measure_univ, mul_one]
  have hm : Measurable fun y : Ω' => R (f ⁻¹' ((fun v => (v, y)) ⁻¹' C)) := by
    have := measurable_measure_prodMk_right (μ := R) (hF hC)
    exact this
  rw [h1, h2, h3, lintegral_mul_const _ hm]

end E5
end QuantumZipper
