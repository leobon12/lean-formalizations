import QuantumZipper.Proofs.Zipper.E5Repair1
import QuantumZipper.Proofs.Zipper.E5ESM3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5 repair, part 6: the E-SM(b) germ facts under a Wiener measure `W` (decision D39)

Restated copies of `E5.map_pathOf_eq_e5`, `E5.esm_level_law` (E5ESM2),
`E5.indepFun_shiftP_pathRestr`, `E5.indep_germ_of_law`, `E5.esm_germ_fields` (E5ESM3), whose
committed versions assume the unsatisfiable `IsBrownianReal (fun t b => b t) W`
(`E5Final4.not_isBrownianReal_coord`). Here `W` is only a Wiener coordinate measure
(`IsPreBrownianReal`). The committed proofs used `hW` only through `hW.toIsPreBrownianReal`, so
they are reproduced verbatim (and `map_pathOf_eq_e5'` is `E5.wiener_eq_map`).
Source: Sheffield arXiv:1012.4797, §5.4 (as for the committed versions).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov

section ESMLawRepair

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
/-- The path law of a Brownian motion is any Wiener coordinate measure. -/
lemma map_pathOf_eq_e5' (hB : IsBrownianReal B P) {W : Measure (ℝ≥0 → ℝ)}
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) : P.map (pathOf B) = W :=
  (wiener_eq_map hW hB).symm

/-- **E-SM(b) on the level space, law form**: under the normalized level measure `𝐑`, the pair
`(V, D)` has law `law(V) ⊗ W`, for every `V` that is `𝓕_{T_ℓ}`-measurable level by level and every
Wiener coordinate measure `W`: the germ `D = smPath B T_ℓ` is a Brownian path independent of
`V`. -/
theorem esm_level_law' (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (μ : Measure ℝ≥0) [SFinite μ]
    (hpos : esmMeas κ T B X P μ univ ≠ 0) (hfin : esmMeas κ T B X P μ univ ≠ ⊤)
    {𝕍 : Type} [MeasurableSpace 𝕍] {V : ℝ≥0 × Ω → 𝕍} (hV : Measurable V)
    (hVT : ∀ ℓ, Measurable[(complLevelStop hκ hκ4 hT hB hX hind hBc ℓ).measurableSpace]
      ((fun ω => V (ℓ, ω)) ∘ ofCompl P))
    {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) :
    (esmRr κ T B X P μ).map
        (fun p : ℝ≥0 × NullMeasurableSpace Ω P => (V (p.1, ofCompl P p.2), esmGerm κ T B X P p)) =
      ((esmRr κ T B X P μ).map
        (fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2))).prod W := by
  have := isProbabilityMeasure_esmRr μ hpos hfin
  have hGm := measurable_esmGerm hκ hκ4 hT hB hX hind hBc
  have hV₁ : Measurable fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2) :=
    hV.comp (measurable_fst.prodMk (measurable_ofCompl.comp measurable_snd))
  have hν : P.map (fun ω => id (pathOf B ω)) = W := map_pathOf_eq_e5' hB hW
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  have h : esmMeas κ T B X P μ
      ((fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2)) ⁻¹' s ∩
        esmGerm κ T B X P ⁻¹' t) =
      W t * esmMeas κ T B X P μ
        ((fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2)) ⁻¹' s) := by
    have h := esmMeas_factor hκ hκ4 hT hB hX hind hBc μ hV hVT measurable_id hs ht
    rw [hν] at h
    exact h
  rw [Measure.map_apply (hV₁.prodMk hGm) (hs.prod ht), Measure.map_apply hV₁ hs,
    Set.mk_preimage_prod, esmRr_apply, esmRr_apply, h]
  ring

end ESMLawRepair

section GermRepair

/-- Simple Markov property of the Brownian coordinate process at `u₀`. -/
lemma indepFun_shiftP_pathRestr' {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) (u₀ : ℝ≥0) :
    IndepFun (shiftP u₀) (pathRestr u₀) W :=
  hW.indepFun_shift u₀

/-- **Germ restriction vs. `(U, D^{+u₀})`**: if `(U, D)` has law `law(U) ⊗ W` (`W` a Wiener
coordinate measure), then `D|_{[0,u₀]}` is Brownian on `[0,u₀]` and independent of
`(U, D^{+u₀})`. -/
theorem indep_germ_of_law' {Ω₁ 𝕌 : Type} [MeasurableSpace Ω₁] [MeasurableSpace 𝕌]
    (R : Measure Ω₁) [IsProbabilityMeasure R] {U : Ω₁ → 𝕌} {D : Ω₁ → ℝ≥0 → ℝ}
    (hU : Measurable U) (hD : Measurable D) {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    (hlaw : R.map (fun ω => (U ω, D ω)) = (R.map U).prod W) (u₀ : ℝ≥0) :
    IndepFun (fun ω => (U ω, shiftP u₀ (D ω))) (fun ω => pathRestr u₀ (D ω)) R ∧
      R.map (fun ω => pathRestr u₀ (D ω)) = W.map (pathRestr u₀) := by
  have hZ : Measurable fun ω => (U ω, D ω) := hU.prodMk hD
  constructor
  · have h := indepFun_prod_fst_e5 (μ := R.map U) (measurable_shiftP u₀)
      (measurable_pathRestr u₀) (indepFun_shiftP_pathRestr' hW u₀)
    rw [← hlaw] at h
    exact indepFun_comp_of_map_e5 hZ
      (measurable_fst.prodMk ((measurable_shiftP u₀).comp measurable_snd))
      ((measurable_pathRestr u₀).comp measurable_snd) h
  · have e : (fun ω => pathRestr u₀ (D ω)) =
        (pathRestr u₀ ∘ Prod.snd) ∘ (fun ω => (U ω, D ω)) := rfl
    rw [e, ← Measure.map_map ((measurable_pathRestr u₀).comp measurable_snd) hZ, hlaw,
      ← Measure.map_map (measurable_pathRestr u₀) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **E5-ESM: the germ fields of the zoom model.** On `(ℝ≥0 × Ω̄) × Ω'` with the reference
measure `𝐑 ⊗ P'`: the germ `D = smPath B T_ℓ` restricted to `[0, u₀]` is Brownian
(`hDW`) and independent of `Φ((V, ω'), D^{+u₀})` for every measurable `Φ` (`hind`), where `V` is
`𝓕_{T_ℓ}`-measurable level by level; `D` is measurable (`hD`) with continuous paths (`hDc`). -/
theorem esm_germ_fields' (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (μ : Measure ℝ≥0) [SFinite μ]
    (hpos : esmMeas κ T B X P μ univ ≠ 0) (hfin : esmMeas κ T B X P μ univ ≠ ⊤)
    {𝕍 : Type} [MeasurableSpace 𝕍] {V : ℝ≥0 × Ω → 𝕍} (hV : Measurable V)
    (hVT : ∀ ℓ, Measurable[(complLevelStop hκ hκ4 hT hB hX hind hBc ℓ).measurableSpace]
      ((fun ω => V (ℓ, ω)) ∘ ofCompl P))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {𝕌 : Type} [MeasurableSpace 𝕌] {Φ : (𝕍 × Ω') × (ℝ≥0 → ℝ) → 𝕌} (hΦ : Measurable Φ)
    (u₀ : ℝ≥0) {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) :
    haveI := isProbabilityMeasure_esmRr μ hpos hfin
    IsProbabilityMeasure ((esmRr κ T B X P μ).prod P') ∧
      IndepFun (fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
          Φ ((V (z.1.1, ofCompl P z.1.2), z.2), shiftP u₀ (esmGerm κ T B X P z.1)))
        (fun z => pathRestr u₀ (esmGerm κ T B X P z.1)) ((esmRr κ T B X P μ).prod P') ∧
      ((esmRr κ T B X P μ).prod P').map (fun z => pathRestr u₀ (esmGerm κ T B X P z.1)) =
        W.map (pathRestr u₀) ∧
      Measurable (fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' => esmGerm κ T B X P z.1) ∧
      ∀ z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω', Continuous (esmGerm κ T B X P z.1) := by
  have := isProbabilityMeasure_esmRr μ hpos hfin
  have hGm := measurable_esmGerm hκ hκ4 hT hB hX hind hBc
  have hV₁ : Measurable fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2) :=
    hV.comp (measurable_fst.prodMk (measurable_ofCompl.comp measurable_snd))
  have hlaw := esm_level_law' hκ hκ4 hT hB hX hind hBc μ hpos hfin hV hVT hW
  -- the germ has law `W` under `𝐑`
  have hDW : (esmRr κ T B X P μ).map (esmGerm κ T B X P) = W := by
    have e : esmGerm κ T B X P = Prod.snd ∘ (fun p : ℝ≥0 × NullMeasurableSpace Ω P =>
        (V (p.1, ofCompl P p.2), esmGerm κ T B X P p)) := rfl
    rw [e, ← Measure.map_map measurable_snd (hV₁.prodMk hGm), hlaw, Measure.map_snd_prod,
      measure_univ, one_smul]
  have hI : IndepFun (fun p : ℝ≥0 × NullMeasurableSpace Ω P => V (p.1, ofCompl P p.2))
      (esmGerm κ T B X P) (esmRr κ T B X P μ) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hV₁.aemeasurable hGm.aemeasurable, hDW]
    exact hlaw
  -- lift to the product with the model factor
  have hF : Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' =>
      (V (z.1.1, ofCompl P z.1.2), z.2) := (hV₁.comp measurable_fst).prodMk measurable_snd
  have hD' : Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' => esmGerm κ T B X P z.1 :=
    hGm.comp measurable_fst
  have hI' := indepFun_prod_snd_e5 (P' := P') hV₁ hGm hI
  have hDW' : ((esmRr κ T B X P μ).prod P').map
      (fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' => esmGerm κ T B X P z.1) = W := by
    rw [show (fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' => esmGerm κ T B X P z.1) =
        esmGerm κ T B X P ∘ Prod.fst from rfl, ← Measure.map_map hGm measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul, hDW]
  have hlaw' := (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hD'.aemeasurable).1 hI'
  rw [hDW'] at hlaw'
  obtain ⟨hInd, hL⟩ := indep_germ_of_law' _ hF hD' hW hlaw' u₀
  exact ⟨inferInstance, hInd.comp hΦ measurable_id, hL, hD', fun z => continuous_esmGerm hBc z.1⟩

end GermRepair

end E5
end QuantumZipper
