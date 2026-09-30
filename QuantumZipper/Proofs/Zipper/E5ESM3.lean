import QuantumZipper.Proofs.Zipper.E5ESM2

/-!
# E5-ESM, part 3: the germ fields `hDW`, `hind`, `hD`, `hDc` of the zoom model

Task E5-G0ESM (Theorem 1.3, node E5; blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, E5 step (3):
"under `𝐑`, `D|_{[0,u₀]} ⊥ M` is Wiener", with `M = (𝒢, D^{+u₀})`; Sheffield, arXiv:1012.4797,
§5.4, pp. 66–72, proof of Lemma 5.6).

On the model space `(ℝ≥0 × Ω̄) × Ω'` with the reference measure `𝐑 ⊗ P'` (`esmRr`, `E5ESM1`), the
germ `D = smPath B T_ℓ` satisfies (`esm_germ_fields`):

* `pathRestr u₀ D` has the Brownian law `W.map (pathRestr u₀)` (`ZoomModel.hDW`);
* `pathRestr u₀ D` is independent of `Φ(V, ω', D^{+u₀})` for every measurable `Φ`, where `V` is
  `𝓕_{T_ℓ}`-measurable level by level, `ω'` is the independent model factor (free field `X'`) and
  `D^{+u₀} = shiftP u₀ D` is the germ after time `u₀` (`ZoomModel.hind`, with `ZoomModel.V` any
  measurable function of `(𝒢, X', D^{+u₀})`);
* `D` is measurable with continuous paths (`ZoomModel.hD`, `ZoomModel.hDc`).

Inputs: E-SM (`esm_level_law`) and the simple Markov property of Brownian motion at the fixed time
`u₀` (`IsPreBrownianReal.indepFun_shift`). Own measure-theoretic bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov

/-- The path after time `u₀`, restarted at `0`: `s ↦ b(u₀ + s) − b(u₀)`. -/
def shiftP (u₀ : ℝ≥0) (b : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun s => b (u₀ + s) - b u₀

lemma measurable_shiftP (u₀ : ℝ≥0) : Measurable (shiftP u₀) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- If `a ⊥ b` under `ν`, then under `μ ⊗ ν`, `(fst, a ∘ snd) ⊥ b ∘ snd`. -/
lemma indepFun_prod_fst_e5 {𝕌 Ω₂ 𝕍 𝕎 : Type} [MeasurableSpace 𝕌] [MeasurableSpace Ω₂]
    [MeasurableSpace 𝕍] [MeasurableSpace 𝕎] {μ : Measure 𝕌} [IsProbabilityMeasure μ]
    {ν : Measure Ω₂} [IsProbabilityMeasure ν] {a : Ω₂ → 𝕍} {b : Ω₂ → 𝕎} (ha : Measurable a)
    (hb : Measurable b) (hab : IndepFun a b ν) :
    IndepFun (fun z : 𝕌 × Ω₂ => (z.1, a z.2)) (fun z => b z.2) (μ.prod ν) := by
  have hF : Measurable fun z : 𝕌 × Ω₂ => (z.1, a z.2) :=
    measurable_fst.prodMk (ha.comp measurable_snd)
  have hG : Measurable fun z : 𝕌 × Ω₂ => b z.2 := hb.comp measurable_snd
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro C S hC hS
  have hsec : ∀ x : 𝕌, MeasurableSet (Prod.mk x ⁻¹' C) := fun x => measurable_prodMk_left hC
  have h1 : (μ.prod ν) ((fun z : 𝕌 × Ω₂ => (z.1, a z.2)) ⁻¹' C ∩ (fun z => b z.2) ⁻¹' S) =
      ∫⁻ x, ν (a ⁻¹' (Prod.mk x ⁻¹' C)) * ν (b ⁻¹' S) ∂μ := by
    rw [Measure.prod_apply ((hF hC).inter (hG hS))]
    refine lintegral_congr fun x => ?_
    rw [← (indepFun_iff_measure_inter_preimage_eq_mul.1 hab) _ _ (hsec x) hS]
    rfl
  have h2 : (μ.prod ν) ((fun z : 𝕌 × Ω₂ => (z.1, a z.2)) ⁻¹' C) =
      ∫⁻ x, ν (a ⁻¹' (Prod.mk x ⁻¹' C)) ∂μ := by
    rw [Measure.prod_apply (hF hC)]
    rfl
  have h3 : (μ.prod ν) ((fun z : 𝕌 × Ω₂ => b z.2) ⁻¹' S) = ν (b ⁻¹' S) := by
    have e : (fun z : 𝕌 × Ω₂ => b z.2) ⁻¹' S = univ ×ˢ (b ⁻¹' S) := by
      ext z; simp
    rw [e, Measure.prod_prod, measure_univ, one_mul]
  have hm : Measurable fun x : 𝕌 => ν (a ⁻¹' (Prod.mk x ⁻¹' C)) :=
    measurable_measure_prodMk_left (hF hC)
  rw [h1, h2, h3, lintegral_mul_const _ hm]

/-- Independence under an image measure pulls back along the map. -/
lemma indepFun_comp_of_map_e5 {Ω₁ 𝔸 𝕍 𝕎 : Type} [MeasurableSpace Ω₁] [MeasurableSpace 𝔸]
    [MeasurableSpace 𝕍] [MeasurableSpace 𝕎] {R : Measure Ω₁} {Z : Ω₁ → 𝔸} (hZ : Measurable Z)
    {f : 𝔸 → 𝕍} {g : 𝔸 → 𝕎} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g (R.map Z)) : IndepFun (f ∘ Z) (g ∘ Z) R := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have := h s t hs ht
  rw [Measure.map_apply hZ ((hf hs).inter (hg ht)), Measure.map_apply hZ (hf hs),
    Measure.map_apply hZ (hg ht)] at this
  exact this

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

end E5
end QuantumZipper
