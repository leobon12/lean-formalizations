import QuantumZipper.Proofs.Probability.LengthMarkov

/-!
# E5-DENS: the germ-density lemma under a weighted reference measure

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, node **E5**, steps (3)–(4): under the reference
measure `𝐑` of E-SM(b) the germ `D|_{[0,u₀]}` of the collided driver is a Wiener path independent of
the conditioning data `V` (the `𝐑`-analogue of `(M, U)`), and the Palm law is `𝐏 = w · 𝐑`. Then the
conditional law of `D|_{[0,u₀]}` given `V` under `𝐏` has a density `ψ(V, ·)` with respect to Wiener
measure (Bayes' formula), so the germ-density lemma E5a
(`LengthMarkov.GermDensity.germDensity_core`) applies under `𝐏`.

* `E5.hlaw_withDensity` : Bayes' formula in the form of the `hlaw` hypothesis of E5a, with the
  explicit density `ψ(v, b) = φ(v, b|_{[0,u₀]}) / ∫ φ(v, ·) dW` (and `ψ = 1` where the
  normalizer is `0` or `∞`), `φ` the Radon–Nikodym derivative of the `𝐏`-law of
  `(V, D|_{[0,u₀]})` with respect to the product law `law_𝐑(V) ⊗ Wiener|_{[0,u₀]}`.
* `E5.germDensity_withDensity` : E5a under `𝐏 = w · 𝐑`.

Here `𝐑` is a probability measure (the consumer normalizes `(dℓ ⊗ P)|_{ℓ ≤ n, tᴸ ℓ ≤ T}`).
**Own elementary argument** (Bayes' formula via Radon–Nikodym and Fubini; blueprint route, the
paper uses Girsanov/Williams time reversal instead: Sheffield, arXiv:1012.4797, §5.4).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

set_option linter.unusedSectionVars false

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity

variable {Ω : Type*} [MeasurableSpace Ω] {R : Measure Ω} [IsProbabilityMeasure R]
  {𝕍 : Type*} [MeasurableSpace 𝕍] {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]

/-- The Radon–Nikodym density of the `(R.withDensity w)`-law of `(V, D|_{[0,u₀]})` with respect to
`law_R(V) ⊗ W|_{[0,u₀]}`. -/
def phiD (R : Measure Ω) (W : Measure (ℝ≥0 → ℝ)) (V : Ω → 𝕍) (D : Ω → ℝ≥0 → ℝ) (u₀ : ℝ≥0)
    (w : Ω → ℝ≥0∞) : 𝕍 × (Iic u₀ → ℝ) → ℝ≥0∞ :=
  ((R.withDensity w).map (fun ω => (V ω, pathRestr u₀ (D ω)))).rnDeriv
    ((R.map V).prod (W.map (pathRestr u₀)))

/-- Its `v`-marginal normalizer. -/
def gD (R : Measure Ω) (W : Measure (ℝ≥0 → ℝ)) (V : Ω → 𝕍) (D : Ω → ℝ≥0 → ℝ) (u₀ : ℝ≥0)
    (w : Ω → ℝ≥0∞) (v : 𝕍) : ℝ≥0∞ :=
  ∫⁻ y, phiD R W V D u₀ w (v, y) ∂(W.map (pathRestr u₀))

open Classical in
/-- The conditional density `ψ(v, b)` of `D|_{[0,u₀]}` given `V = v` under `R.withDensity w`. -/
def psiD (R : Measure Ω) (W : Measure (ℝ≥0 → ℝ)) (V : Ω → 𝕍) (D : Ω → ℝ≥0 → ℝ) (u₀ : ℝ≥0)
    (w : Ω → ℝ≥0∞) (v : 𝕍) (b : ℝ≥0 → ℝ) : ℝ :=
  if gD R W V D u₀ w v = 0 ∨ gD R W V D u₀ w v = ⊤ then 1
  else (phiD R W V D u₀ w (v, pathRestr u₀ b)).toReal / (gD R W V D u₀ w v).toReal

variable {V : Ω → 𝕍} {D : Ω → ℝ≥0 → ℝ} {u₀ : ℝ≥0} {w : Ω → ℝ≥0∞}

lemma measurable_phiD : Measurable (phiD R W V D u₀ w) := Measure.measurable_rnDeriv _ _

lemma measurable_gD : Measurable (gD R W V D u₀ w) :=
  (measurable_phiD (R := R) (W := W) (V := V) (D := D) (u₀ := u₀) (w := w)).lintegral_prod_right'

lemma measurable_psiD :
    Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => psiD R W V D u₀ w p.1 p.2) := by
  classical
  unfold psiD
  refine Measurable.ite ?_ measurable_const ?_
  · exact (measurable_gD.comp measurable_fst) (measurableSet_singleton 0) |>.union
      ((measurable_gD.comp measurable_fst) (measurableSet_singleton ⊤))
  · exact ((measurable_phiD.comp (measurable_fst.prodMk
      ((measurable_pathRestr u₀).comp measurable_snd))).ennreal_toReal).div
      ((measurable_gD.comp measurable_fst).ennreal_toReal)

lemma psiD_nonneg (v : 𝕍) (b : ℝ≥0 → ℝ) : 0 ≤ psiD R W V D u₀ w v b := by
  unfold psiD; split_ifs
  · exact zero_le_one
  · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma integral_psiD (v : 𝕍) : ∫ b, psiD R W V D u₀ w v b ∂W = 1 := by
  classical
  by_cases h : gD R W V D u₀ w v = 0 ∨ gD R W V D u₀ w v = ⊤
  · simp [psiD, h]
  · push Not at h
    have hm : Measurable fun y => phiD R W V D u₀ w (v, y) :=
      measurable_phiD.comp measurable_prodMk_left
    simp only [psiD, h.1, h.2, or_self, ite_false]
    rw [integral_div]
    have : ∫ b, (phiD R W V D u₀ w (v, pathRestr u₀ b)).toReal ∂W =
        ∫ y, (phiD R W V D u₀ w (v, y)).toReal ∂(W.map (pathRestr u₀)) :=
      (integral_map (measurable_pathRestr u₀).aemeasurable
        hm.ennreal_toReal.aestronglyMeasurable).symm
    rw [this, integral_toReal hm.aemeasurable (ae_lt_top hm h.2)]
    exact div_self (ENNReal.toReal_ne_zero.2 ⟨h.1, h.2⟩)

lemma isProbabilityMeasure_withDensity_of (hw1 : ∫⁻ ω, w ω ∂R = 1) :
    IsProbabilityMeasure (R.withDensity w) :=
  ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hw1]⟩

/-- **Bayes' formula** in the form of the `hlaw` hypothesis of E5a: if under `R` the germ
`D|_{[0,u₀]}` is Wiener-distributed and independent of `V`, then under `R.withDensity w` the
conditional law of `D|_{[0,u₀]}` given `V` has density `psiD … (V ·)` with respect to `W`. -/
theorem hlaw_withDensity (hV : Measurable V) (hD : Measurable D)
    (hind : IndepFun V (fun ω => pathRestr u₀ (D ω)) R)
    (hDW : R.map (fun ω => pathRestr u₀ (D ω)) = W.map (pathRestr u₀))
    (hw1 : ∫⁻ ω, w ω ∂R = 1)
    (Φ : 𝕍 × (Iic u₀ → ℝ) → ℝ) (hΦ : Measurable Φ) (hC : ∃ C, ∀ p, |Φ p| ≤ C) :
    ∫ ω, Φ (V ω, pathRestr u₀ (D ω)) ∂(R.withDensity w) =
      ∫ ω, ∫ b, Φ (V ω, pathRestr u₀ b) * psiD R W V D u₀ w (V ω) b ∂W ∂(R.withDensity w) := by
  classical
  obtain ⟨C, hC⟩ := hC
  have : IsProbabilityMeasure (R.withDensity w) := isProbabilityMeasure_withDensity_of hw1
  have hr : Measurable (pathRestr u₀) := measurable_pathRestr u₀
  have hrD : Measurable (fun ω => pathRestr u₀ (D ω)) := hr.comp hD
  have hf : Measurable (fun ω => (V ω, pathRestr u₀ (D ω))) := hV.prodMk hrD
  have hRf : R.map (fun ω => (V ω, pathRestr u₀ (D ω))) =
      (R.map V).prod (W.map (pathRestr u₀)) := by
    rw [hind.map_prod_eq_prod_map_map hV.aemeasurable hrD.aemeasurable, hDW]
  have hac : (R.withDensity w).map (fun ω => (V ω, pathRestr u₀ (D ω))) ≪
      (R.map V).prod (W.map (pathRestr u₀)) :=
    hRf ▸ (withDensity_absolutelyContinuous R w).map hf
  have hPf : (R.withDensity w).map (fun ω => (V ω, pathRestr u₀ (D ω))) =
      ((R.map V).prod (W.map (pathRestr u₀))).withDensity (phiD R W V D u₀ w) :=
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  have hφm : Measurable (phiD R W V D u₀ w) := measurable_phiD
  have hφ1 : ∫⁻ z, phiD R W V D u₀ w z ∂((R.map V).prod (W.map (pathRestr u₀))) = 1 := by
    have h1 : (((R.map V).prod (W.map (pathRestr u₀))).withDensity (phiD R W V D u₀ w)) univ
        = 1 := by rw [← hPf]; exact measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  have hPV : (R.withDensity w).map V = (R.map V).withDensity (gD R W V D u₀ w) := by
    have hmap : (R.withDensity w).map V =
        ((R.withDensity w).map fun ω => (V ω, pathRestr u₀ (D ω))).map Prod.fst := by
      rw [Measure.map_map measurable_fst hf]; rfl
    ext s hs
    rw [hmap, Measure.map_apply measurable_fst hs, hPf, withDensity_apply _ (measurable_fst hs),
      withDensity_apply _ hs]
    have hprod : Prod.fst ⁻¹' s = s ×ˢ (univ : Set (Iic u₀ → ℝ)) := by ext; simp
    rw [hprod, setLIntegral_prod _ hφm.aemeasurable]
    simp only [Measure.restrict_univ, gD]
  have hg1 : ∫⁻ v, gD R W V D u₀ w v ∂(R.map V) = 1 := by
    have h1 : ((R.map V).withDensity (gD R W V D u₀ w)) univ = 1 := by
      rw [← hPV]; exact measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  have hgfin : ∀ᵐ v ∂(R.map V), gD R W V D u₀ w v < ⊤ :=
    ae_lt_top measurable_gD (by rw [hg1]; exact ENNReal.one_ne_top)
  -- the left side
  have hL : ∫ ω, Φ (V ω, pathRestr u₀ (D ω)) ∂(R.withDensity w) =
      ∫ v, ∫ y, (phiD R W V D u₀ w (v, y)).toReal * Φ (v, y) ∂(W.map (pathRestr u₀))
        ∂(R.map V) := by
    rw [← integral_map hf.aemeasurable hΦ.aestronglyMeasurable, hPf,
      integral_withDensity_eq_integral_toReal_smul hφm
        (ae_lt_top hφm (by rw [hφ1]; exact ENNReal.one_ne_top))]
    simp only [smul_eq_mul]
    refine integral_prod (fun z => (phiD R W V D u₀ w z).toReal * Φ z) ?_
    refine Integrable.mono' ((integrable_toReal_of_lintegral_ne_top hφm.aemeasurable
      (by rw [hφ1]; exact ENNReal.one_ne_top)).mul_const C)
      (hφm.ennreal_toReal.mul hΦ).aestronglyMeasurable ?_
    filter_upwards with z
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hC z) ENNReal.toReal_nonneg
  -- the right side
  have hFm : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) =>
      Φ (p.1, pathRestr u₀ p.2) * psiD R W V D u₀ w p.1 p.2) :=
    (hΦ.comp (measurable_fst.prodMk (hr.comp measurable_snd))).mul measurable_psiD
  have hH : StronglyMeasurable (fun v => ∫ b, Φ (v, pathRestr u₀ b) *
      psiD R W V D u₀ w v b ∂W) :=
    hFm.stronglyMeasurable.integral_prod_right'
  rw [hL, ← integral_map hV.aemeasurable hH.aestronglyMeasurable, hPV,
    integral_withDensity_eq_integral_toReal_smul measurable_gD hgfin]
  simp only [smul_eq_mul]
  refine integral_congr_ae ?_
  filter_upwards [hgfin] with v hv
  have hm : Measurable fun y => phiD R W V D u₀ w (v, y) := hφm.comp measurable_prodMk_left
  by_cases h0 : gD R W V D u₀ w v = 0
  · rw [h0, ENNReal.toReal_zero, zero_mul]
    have h0' : (fun y => phiD R W V D u₀ w (v, y)) =ᵐ[W.map (pathRestr u₀)] 0 :=
      (lintegral_eq_zero_iff hm).1 h0
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0'] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]
  · have hne : ¬ (gD R W V D u₀ w v = 0 ∨ gD R W V D u₀ w v = ⊤) := by
      simp [h0, hv.ne]
    simp only [psiD, hne, ite_false]
    have hmap : ∫ b, Φ (v, pathRestr u₀ b) * ((phiD R W V D u₀ w (v, pathRestr u₀ b)).toReal /
          (gD R W V D u₀ w v).toReal) ∂W =
        ∫ y, Φ (v, y) * ((phiD R W V D u₀ w (v, y)).toReal / (gD R W V D u₀ w v).toReal)
          ∂(W.map (pathRestr u₀)) :=
      (integral_map hr.aemeasurable (((hΦ.comp measurable_prodMk_left).mul
        (hm.ennreal_toReal.div_const _)).aestronglyMeasurable)).symm
    rw [hmap, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hc : (gD R W V D u₀ w v).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, hv.ne⟩
    simp only
    field_simp

end E5
end QuantumZipper
