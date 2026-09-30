import QuantumZipper.Proofs.Zipper.E5ESM3
import QuantumZipper.Proofs.Zipper.ESMLenLRID

/-!
# E5-ESM, part 4: the Palm measure as a density against the level measure

Task E5-G0ESM (Theorem 1.3, node E5; blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E-SM(b):
"`𝐏|_{τ_x ≤ T} = w · 𝐑` with `w = Z⁻¹ e^{−γm/2} 1{−δ ≤ x(ℓ)}`"; Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72, proof of Lemma 5.6).

`palm_eq_level`: for every test `G ≥ 0` of `(ω, x, 𝒞_x)`, the Palm integral
`∫ dP ∫_{[−δ,0]} 1{τ_x < T} G(ω, x, 𝒞_x) dν_ω` equals the integral against the level measure
`esmMeas κ T B X P lvlMu` (`E5ESM1`, level law `lvlMu = e^{−ℓ} dℓ` on `ℓ > 0`) of

`lvlF G (ℓ, ω) = e^{ℓ} e^{−γ m/2} 1{ℓ < L⁻_T, −δ ≤ x(ℓ)} G(ω, x(ℓ), zipCapDown γ T_ℓ 𝒵)`,

`x(ℓ) = 0₋(T − T_ℓ)` (`xL`). So the Palm law is `lvlF · 𝐑` up to the constant `𝐑`-normalizer:
the germ fields of `E5ESM3` (Brownian germ independent of `𝒢`) are available under the Palm
measure through this density, which is the Bayes structure `Q = Rr.withDensity w` of
`E5.ZoomModel`. The collided configuration at `x(ℓ)` is `zipCapDown γ T_ℓ 𝒵`, whose driver is
`drvMap κ (smPath B T_ℓ)` (`ESM.zipCapDown_cfg_snd`), i.e. `√κ` times the germ `esmGerm`.

Inputs: LR-ID with the E-SM stopping times (`Wire2.ae_lr_id_levelTime`, proved); the joint
measurability of the level integrand is an explicit hypothesis (`hFm`). Change of variables
bookkeeping (`ℓ ∈ (0,∞)` ↔ `ℝ≥0`, Tonelli) is own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- The level law `e^{−ℓ} dℓ` on `ℓ > 0`, carried to `ℝ≥0`. -/
def lvlMu : Measure ℝ≥0 :=
  ((volume.restrict (Ioi (0 : ℝ))).withDensity fun x => ENNReal.ofReal (Real.exp (-x))).map
    Real.toNNReal

instance : SFinite lvlMu := by unfold lvlMu; infer_instance

/-- The Palm point at level `ℓ`: `x(ℓ) = 0₋(T − T_ℓ)`. -/
def xL (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ℓ : ℝ≥0) (ω : Ω) : ℝ :=
  zeroMinus (B2.Vr κ T B ω) (T - levelTime (lenA κ T B X) T.toNNReal ℓ ω)

/-- The level integrand of a Palm test `G`. -/
def lvlF (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ) (δ : ℝ)
    (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞) (ℓ : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ℓ) *
    (ENNReal.ofReal (Real.exp (Real.sqrt κ * -(E1.mReg κ T B X ϖ ω) / 2)) *
      {ℓ : ℝ≥0 | (ℓ : ℝ≥0∞) < lenA κ T B X T.toNNReal ω ∧ -δ ≤ xL κ T B X ℓ ω}.indicator
        (fun ℓ => G ω (xL κ T B X ℓ ω)
          (zipCapDown (Real.sqrt κ) (levelTime (lenA κ T B X) T.toNNReal ℓ ω)
            (B2.cfg κ B X ω))) ℓ)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- One `ω` at a time: the `ℓ > 0` Lebesgue integral of LR-ID is the `lvlMu` integral of
`lvlF`. -/
lemma lintegral_lvlMu_lvlF (ϖ : Measure ℂ) (δ : ℝ) (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞)
    (ω : Ω) (hm : Measurable fun ℓ : ℝ≥0 => lvlF κ T B X ϖ δ G ℓ ω) :
    ENNReal.ofReal (Real.exp (Real.sqrt κ * -(E1.mReg κ T B X ϖ ω) / 2)) *
        ∫⁻ ℓ in Ioi (0 : ℝ),
          {ℓ | ENNReal.ofReal ℓ < lenA κ T B X T.toNNReal ω ∧
              -δ ≤ zeroMinus (B2.Vr κ T B ω)
                (T - levelTime (lenA κ T B X) T.toNNReal ℓ.toNNReal ω)}.indicator
            (fun ℓ => G ω (zeroMinus (B2.Vr κ T B ω)
                (T - levelTime (lenA κ T B X) T.toNNReal ℓ.toNNReal ω))
              (zipCapDown (Real.sqrt κ) (levelTime (lenA κ T B X) T.toNNReal ℓ.toNNReal ω)
                (B2.cfg κ B X ω))) ℓ =
      ∫⁻ ℓ, lvlF κ T B X ϖ δ G ℓ ω ∂lvlMu := by
  rw [lvlMu, lintegral_map hm measurable_real_toNNReal,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ℓ hℓ => ?_
  have hℓ' : (0 : ℝ) < ℓ := hℓ
  have hcoe : ((ℓ.toNNReal : ℝ≥0) : ℝ) = ℓ := Real.coe_toNNReal _ hℓ'.le
  simp only [Pi.mul_apply, lvlF, xL, hcoe]
  have he : ENNReal.ofReal (Real.exp (-ℓ)) * ENNReal.ofReal (Real.exp ℓ) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  by_cases hA : ℓ.toNNReal ∈ {ℓ : ℝ≥0 | (ℓ : ℝ≥0∞) < lenA κ T B X T.toNNReal ω ∧
      -δ ≤ zeroMinus (B2.Vr κ T B ω) (T - levelTime (lenA κ T B X) T.toNNReal ℓ ω)}
  · have hA' : ℓ ∈ {ℓ : ℝ | ENNReal.ofReal ℓ < lenA κ T B X T.toNNReal ω ∧
        -δ ≤ zeroMinus (B2.Vr κ T B ω)
          (T - levelTime (lenA κ T B X) T.toNNReal ℓ.toNNReal ω)} := hA
    rw [indicator_of_mem hA, indicator_of_mem hA', ← mul_assoc, he, one_mul]
  · have hA' : ℓ ∉ {ℓ : ℝ | ENNReal.ofReal ℓ < lenA κ T B X T.toNNReal ω ∧
        -δ ≤ zeroMinus (B2.Vr κ T B ω)
          (T - levelTime (lenA κ T B X) T.toNNReal ℓ.toNNReal ω)} := hA
    rw [indicator_of_notMem hA, indicator_of_notMem hA']
    simp

/-- **The Palm integral as a level integral (E-SM(b), `𝐏|_{τ_x<T} = w · 𝐑`).** For every Palm
test `G` whose level integrand is jointly measurable on the level space, the Palm integral of
`1{τ_x < T} G(ω, x, 𝒞_x)` over `x ∈ [−δ, 0]` equals the integral of `lvlF G` against the level
measure `esmMeas κ T B X P lvlMu`. -/
theorem palm_eq_level (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (ϖ : Measure ℂ) (δ : ℝ)
    (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞)
    (hFm : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      lvlF κ T B X ϖ δ G z.1 (ofCompl P z.2)) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}.indicator
        (fun x => G ω x (B2.collided κ T B X ω x)) x ∂E1.nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ z, lvlF κ T B X ϖ δ G z.1 (ofCompl P z.2) ∂esmMeas κ T B X P lvlMu := by
  have hE := measurableSet_esmEvt hκ hκ4 hT hB hX hind hBc
  rw [lintegral_congr_ae (Wire2.ae_lr_id_levelTime hκ hκ4 hT hB hX hind ϖ δ G), esmMeas,
    ← lintegral_indicator hE, lintegral_prod_symm' _ (hFm.indicator hE),
    ← lintegral_completion (P := P)]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_lvlMu_lvlF ϖ δ G (ofCompl P ω) (hFm.comp measurable_prodMk_right)]
  refine lintegral_congr fun ℓ => ?_
  by_cases hℓ : (ℓ, ω) ∈ esmEvt κ T B X P
  · rw [indicator_of_mem hℓ]
  · rw [indicator_of_notMem hℓ]
    have hn : ℓ ∉ {ℓ : ℝ≥0 | (ℓ : ℝ≥0∞) < lenA κ T B X T.toNNReal (ofCompl P ω) ∧
        -δ ≤ xL κ T B X ℓ (ofCompl P ω)} := fun h => hℓ (le_of_lt h.1)
    simp only [lvlF, indicator_of_notMem hn, mul_zero]

end E5
end QuantumZipper
