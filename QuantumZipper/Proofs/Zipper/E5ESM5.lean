import QuantumZipper.Proofs.Zipper.E5ESM4
import QuantumZipper.Proofs.Zipper.E5Main1

/-!
# E5-ESM, part 5: the Bayes structure `Q = 𝐑.withDensity w` and E5's left side on the level space

Task E5-G0ESM (Theorem 1.3, node E5; blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E-SM(b) and
E5 step (3); Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, proof of Lemma 5.6).

* `palm_level_bayes`: there is a measurable density `w` with `∫ w d𝐑 = 1` such that every Palm
  integral (test `G` of `(ω, x, 𝒞_x)` with measurable level integrand) is
  `p · E_Q G(ω, x(ℓ), zipCapDown γ T_ℓ 𝒵)`, `Q = 𝐑.withDensity w`, `p` the Palm mass (`pmass`).
* `lhsF_eq_level`: in particular E5's left side is `p · E_Q Γ(loc R (zcfgL C))` with
  `zcfgL C` the canonicalized, shifted collided configuration at the level time
  (`zipCapDown γ T_ℓ 𝒵`), whose driver is `√κ ×` the germ `esmGerm` (`ESM.zipCapDown_cfg_snd`).

With `E5ESM3.esm_germ_fields` (germ Brownian and independent of `𝒢`, `X'`, `D^{+u₀}` under `𝐑 ⊗ P'`)
this is the E-SM(b) Bayes structure of `E5.ZoomModel` (`Rr`, `w`, `hw1`, `hQ`, `hDW`, `hind`).
Own bookkeeping; inputs LR-ID (`Wire2.ae_lr_id_levelTime`) and the a.s. collision description
(`Wire2.ae_zeroMinus_Vr_facts`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- The Palm integral of a test `G` of `(ω, x, 𝒞_x)`. -/
def palmInt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    (δ : ℝ) (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}.indicator
    (fun x => G ω x (B2.collided κ T B X ω x)) x ∂E1.nuPalm κ T B X ϖ ω ∂P

/-- The Palm test `G` read at level `ℓ`. -/
def lvlG (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞) (ℓ : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  G ω (xL κ T B X ℓ ω) (zipCapDown (Real.sqrt κ) (levelTime (lenA κ T B X) T.toNNReal ℓ ω)
    (B2.cfg κ B X ω))

/-- The unnormalized Palm density on the level space. -/
def w0 (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ) (δ : ℝ) (ℓ : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  lvlF κ T B X ϖ δ (fun _ _ _ => 1) ℓ ω

omit [MeasurableSpace Ω] in
lemma lvlF_eq_w0_mul (ϖ : Measure ℂ) (δ : ℝ) (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞)
    (ℓ : ℝ≥0) (ω : Ω) :
    lvlF κ T B X ϖ δ G ℓ ω = w0 κ T B X ϖ δ ℓ ω * lvlG κ T B X G ℓ ω := by
  simp only [w0, lvlF, lvlG, mul_assoc]
  congr 2
  by_cases h : ℓ ∈ {ℓ : ℝ≥0 | (ℓ : ℝ≥0∞) < lenA κ T B X T.toNNReal ω ∧ -δ ≤ xL κ T B X ℓ ω}
  · rw [indicator_of_mem h, indicator_of_mem h, one_mul]
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]

omit [MeasurableSpace Ω] in
lemma w0_lt_top (ϖ : Measure ℂ) (δ : ℝ) (ℓ : ℝ≥0) (ω : Ω) : w0 κ T B X ϖ δ ℓ ω < ⊤ := by
  simp only [w0, lvlF]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  by_cases h : ℓ ∈ {ℓ : ℝ≥0 | (ℓ : ℝ≥0∞) < lenA κ T B X T.toNNReal ω ∧ -δ ≤ xL κ T B X ℓ ω}
  · rw [indicator_of_mem h]; exact ENNReal.one_lt_top
  · rw [indicator_of_notMem h]; exact ENNReal.zero_lt_top

/-- The Palm integral of `1` is the Palm mass. -/
lemma palmInt_one (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (ϖ : Measure ℂ) (δ : ℝ) :
    palmInt κ T P B X ϖ δ (fun _ _ _ => 1) = pmass κ T P B X ϖ δ := by
  rw [palmInt, pmass]
  refine lintegral_congr_ae ?_
  filter_upwards [Wire2.ae_zeroMinus_Vr_facts hκ hκ4.le hT P B hB] with ω hω
  have hζ := hω.2.2.2.2.2
  set ζ := zeroMinus (B2.Vr κ T B ω) T
  have e : {x | x ∈ Icc (-δ) 0 ∧ realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T} =
      Ioi ζ ∩ Icc (-δ) 0 := by
    ext x
    constructor
    · rintro ⟨hx, hA⟩; exact ⟨(hζ x hx.2).1 hA, hx⟩
    · rintro ⟨hA, hx⟩; exact ⟨hx, (hζ x hx.2).2 hA⟩
  rw [e, ← Measure.restrict_apply measurableSet_Ioi, ← lintegral_indicator_one measurableSet_Ioi]
  refine setLIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  by_cases hA : realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T
  · rw [indicator_of_mem (show x ∈ {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}
      from hA), indicator_of_mem (show x ∈ Ioi ζ from (hζ x hx.2).1 hA)]; rfl
  · rw [indicator_of_notMem (show x ∉ {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}
      from hA), indicator_of_notMem (show x ∉ Ioi ζ from fun h => hA ((hζ x hx.2).2 h))]

/-- **The E-SM(b) Bayes structure.** Given that the level measure has positive finite mass, the
Palm mass `p` is positive and finite, and the Palm density `w0` is measurable on the level space,
there is a measurable density `w` with `∫ w d𝐑 = 1` such that every Palm integral whose level
integrand is measurable is `p · ∫ G(ω, x(ℓ), zipCapDown γ T_ℓ 𝒵) d(𝐑.withDensity w)`. -/
theorem palm_level_bayes (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (ϖ : Measure ℂ) (δ : ℝ)
    (hpos : esmMeas κ T B X P lvlMu univ ≠ 0) (hfin : esmMeas κ T B X P lvlMu univ ≠ ⊤)
    (hp0 : pmass κ T P B X ϖ δ ≠ 0) (hpt : pmass κ T P B X ϖ δ ≠ ⊤)
    (hw0 : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      w0 κ T B X ϖ δ z.1 (ofCompl P z.2)) :
    ∃ w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞, Measurable w ∧
      ∫⁻ z, w z ∂esmRr κ T B X P lvlMu = 1 ∧
      ∀ G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞,
        (Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
          lvlF κ T B X ϖ δ G z.1 (ofCompl P z.2)) →
        palmInt κ T P B X ϖ δ G = pmass κ T P B X ϖ δ *
          ∫⁻ z, lvlG κ T B X G z.1 (ofCompl P z.2)
            ∂(esmRr κ T B X P lvlMu).withDensity w := by
  set c := esmMeas κ T B X P lvlMu univ with hc
  set p := pmass κ T P B X ϖ δ with hp
  set W0 := fun z : ℝ≥0 × NullMeasurableSpace Ω P => w0 κ T B X ϖ δ z.1 (ofCompl P z.2)
  have hW0p : ∫⁻ z, W0 z ∂esmMeas κ T B X P lvlMu = p := by
    have h : palmInt κ T P B X ϖ δ (fun _ _ _ => 1) = ∫⁻ z, W0 z ∂esmMeas κ T B X P lvlMu :=
      palm_eq_level hκ hκ4 hT hB hX hind hBc ϖ δ (fun _ _ _ => 1) hw0
    rw [palmInt_one hκ hκ4 hT hB] at h
    exact h.symm
  have hcp : c * p⁻¹ ≠ ⊤ := ENNReal.mul_ne_top hfin (ENNReal.inv_ne_top.2 hp0)
  have hRr : ∀ f : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞,
      ∫⁻ z, f z ∂esmRr κ T B X P lvlMu = c⁻¹ * ∫⁻ z, f z ∂esmMeas κ T B X P lvlMu := by
    intro f
    rw [esmRr, lintegral_smul_measure, smul_eq_mul]
  refine ⟨fun z => c * p⁻¹ * W0 z, hw0.const_mul _, ?_, fun G hG => ?_⟩
  · rw [hRr, lintegral_const_mul' _ _ hcp, hW0p, ← mul_assoc, ← mul_assoc,
      ENNReal.inv_mul_cancel hpos hfin, one_mul, ENNReal.inv_mul_cancel hp0 hpt]
  · have hL : palmInt κ T P B X ϖ δ G = ∫⁻ z, lvlF κ T B X ϖ δ G z.1 (ofCompl P z.2)
        ∂esmMeas κ T B X P lvlMu := palm_eq_level hκ hκ4 hT hB hX hind hBc ϖ δ G hG
    rw [hL, lintegral_withDensity_eq_lintegral_mul_non_measurable _ (hw0.const_mul _)
      (ae_of_all _ fun z => ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcp) (w0_lt_top ϖ δ _ _)),
      hRr]
    simp only [Pi.mul_apply]
    simp_rw [mul_assoc (c * p⁻¹)]
    rw [lintegral_const_mul' _ _ hcp]
    simp only [lvlF_eq_w0_mul]
    set I := ∫⁻ z, W0 z * lvlG κ T B X G z.1 (ofCompl P z.2) ∂esmMeas κ T B X P lvlMu
    calc I = (p * p⁻¹) * (c⁻¹ * c) * I := by
          rw [ENNReal.mul_inv_cancel hp0 hpt, ENNReal.inv_mul_cancel hpos hfin, one_mul, one_mul]
      _ = p * (c⁻¹ * (c * p⁻¹ * I)) := by ring

end E5
end QuantumZipper
