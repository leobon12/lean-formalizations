import QuantumZipper.Proofs.Thm18.G3RShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the Palm laws of `B` and `C` seen from region 2

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71 (region 1 integrated out given the field
outside both half-discs; D85 update 18:30). For a function `f` of the region-2 field, the outside
field and the Palm length,
`Z_g ∫ f dP_g = ∫∫ f(ω, ℓ) 1{ℓ > 0} F(ω, ℓ − a_g(ω)) dℓ dP(ω)` (`lintegral_g3pPalm_region2`),
where `a_g = ν₀[−δ, 0]` is the gap part of the Palm mass (outside-measurable) and
`F(ω, v) = P(ν₁[−δ, 0] ≥ v | outside)(ω)` is the conditional tail of the region-1 part
(`g3F`, a regular version, `rcdTail`). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The conditioning σ-algebra (outside both half-discs). -/
abbrev g3O (i : G3Idx) : MeasurableSpace Ω₀ := outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂

/-- The region-1 part of the Palm mass. -/
def g3Y (γ : ℝ) (i : G3Idx) (ω : Ω₀) : ℝ := (g3pν₁ γ (g3wProf γ) i ω (Icc (-i.δ) 0)).toReal

/-- The gap part of the Palm mass. -/
def g3a (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (ω : Ω₀) : ℝ := (g3pν₀ γ g i ω (Icc (-i.δ) 0)).toReal

/-- The conditional tail of the region-1 part given the outside field. -/
def g3F (γ : ℝ) (i : G3Idx) (ω : Ω₀) (v : ℝ) : ℝ≥0∞ := rcdTail (g3O i) gffBase.P (g3Y γ i) ω v

theorem measurable_g3Y (γ : ℝ) (i : G3Idx) :
    Measurable[localSigma X₀ i.t₁ i.r₁ ⊔ g3O i] (g3Y γ i) :=
  ENNReal.measurable_toReal.comp ((Measure.measurable_coe measurableSet_Icc).comp
    ((measurable_bdryM γ).comp (measurable_g3pReg₁ γ (g3wProf γ) i)))

theorem measurable_g3Y' (γ : ℝ) (i : G3Idx) : Measurable (g3Y γ i) :=
  (measurable_g3Y γ i).mono (sup_le (localSigma_le gffBase.gff _ _)
    (outsideSigma2_le gffBase.gff _ _ _ _)) le_rfl

theorem measurable_g3a (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Measurable[g3O i] (g3a γ g i) :=
  ENNReal.measurable_toReal.comp ((Measure.measurable_coe measurableSet_Icc).comp
    ((measurable_bdryM γ).comp (measurable_g3pGap γ g i)))

theorem measurable_g3F (γ : ℝ) (i : G3Idx) :
    Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] fun p : Ω₀ × ℝ => g3F γ i p.1 p.2 :=
  measurable_rcdTail (g3Y γ i)

theorem g3F_le_one (γ : ℝ) (i : G3Idx) (ω : Ω₀) (v : ℝ) : g3F γ i ω v ≤ 1 :=
  rcdTail_le_one _ _ _

/-- `sig₂` is the product σ-algebra of region 2 plus outside, and Borel. -/
theorem sig₂_eq_prod (i : G3Idx) :
    sig₂ i = @Prod.instMeasurableSpace Ω₀ ℝ (localSigma X₀ i.t₂ i.r₂ ⊔ g3O i) _ := by
  show _ = MeasurableSpace.comap Prod.fst (localSigma X₀ i.t₂ i.r₂ ⊔ g3O i) ⊔
    MeasurableSpace.comap Prod.snd _
  rw [MeasurableSpace.comap_sup, sup_assoc]
  rfl

/-- The Palm mass splits into region-1 and gap parts. -/
theorem g3pMass_toReal_eq {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} {ω : Ω₀}
    (h1 : g3pν₁ γ g i ω = g3pν₁ γ (g3wProf γ) i ω) :
    (g3pMass γ g i ω).toReal = g3Y γ i ω + g3a γ g i ω := by
  have hf := g3pm_Icc_lt_top γ g i ω (-i.δ) 0
  rw [Measure.add_apply] at hf
  rw [g3pMass, Measure.add_apply, ENNReal.toReal_add (ENNReal.add_lt_top.1 hf).1.ne
    (ENNReal.add_lt_top.1 hf).2.ne, g3Y, g3a, h1]

theorem measurable_g3pMass (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Measurable (g3pMass γ g i) :=
  ((Measure.measurable_coe measurableSet_Icc).comp (measurable_g3psum₁ γ g i)).mono
    (sup_le (localSigma_le gffBase.gff _ _) (outsideSigma2_le gffBase.gff _ _ _ _)) le_rfl

/-- The Palm domain. -/
def g3D (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : Set (Ω₀ × ℝ) :=
  {p | 0 < p.2 ∧ p.2 ≤ (g3pMass γ g i p.1).toReal}

theorem measurableSet_g3D (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) : MeasurableSet (g3D γ g i) :=
  (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd
    (ENNReal.measurable_toReal.comp ((measurable_g3pMass γ g i).comp measurable_fst)))

/-- **The Palm law as the restricted product measure**, up to the normalization. -/
theorem g3pPalm_smul_eq (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx)
    (hZ : 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤) :
    g3pZ γ g i • g3pPalmLaw γ g i = (gffBase.P.prod volume).restrict (g3D γ g i) := by
  ext S hS
  rw [Measure.smul_apply, smul_eq_mul, g3pPalmLaw_apply_eq_lebesgue _ _ _ hZ hS, ← mul_assoc,
    ENNReal.mul_inv_cancel hZ.1.ne' hZ.2.ne, one_mul, Measure.restrict_apply hS,
    Measure.prod_apply (hS.inter (measurableSet_g3D γ g i))]
  refine lintegral_congr fun ω => ?_
  congr 1

/-- **Function form of the Palm law.** -/
theorem lintegral_g3pPalm (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx)
    (hZ : 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤) {f : Ω₀ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    g3pZ γ g i * ∫⁻ p, f p ∂(g3pPalmLaw γ g i) =
      ∫⁻ ω, ∫⁻ ℓ, (g3D γ g i).indicator f (ω, ℓ) ∂volume ∂gffBase.P := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, g3pPalm_smul_eq γ g i hZ,
    ← lintegral_indicator (measurableSet_g3D γ g i),
    lintegral_prod _ ((hf.indicator (measurableSet_g3D γ g i)).aemeasurable)]

/-- **Region 1 integrated out.** For `f` measurable for region 2, the outside field and the
Palm length, `Z_g ∫ f dP_g = ∫∫ f 1{ℓ > 0} F(ω, ℓ − a_g ω)`. -/
theorem lintegral_g3pPalm_region2 {γ : ℝ} (g : ℂ → ℝ) (i : G3Idx)
    (hZ : 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤)
    (h1 : ∀ ω, g3pν₁ γ g i ω = g3pν₁ γ (g3wProf γ) i ω)
    {f : Ω₀ × ℝ → ℝ≥0∞} (hf : Measurable[sig₂ i] f) :
    g3pZ γ g i * ∫⁻ p, f p ∂(g3pPalmLaw γ g i) =
      ∫⁻ ω, ∫⁻ ℓ, (f (ω, ℓ) * (Ioi 0).indicator 1 ℓ) * g3F γ i ω (ℓ - g3a γ g i ω)
        ∂volume ∂gffBase.P := by
  have hf0 : Measurable f := hf.mono (sig_le_g3 i _ _) le_rfl
  rw [lintegral_g3pPalm γ g i hZ hf0]
  have hfm : Measurable[@Prod.instMeasurableSpace Ω₀ ℝ (localSigma X₀ i.t₂ i.r₂ ⊔ g3O i) _]
      fun p : Ω₀ × ℝ => f p * (Ioi 0).indicator 1 p.2 := by
    rw [← sig₂_eq_prod]
    exact hf.mul ((measurable_const.indicator measurableSet_Ioi).comp
      (measurable_snd_palm (X := X₀) (t := i.t₂) (r := i.r₂)))
  have e := lintegral_threshold_eq (P := gffBase.P) (localSigma_le gffBase.gff i.t₁ i.r₁)
    (localSigma_le gffBase.gff i.t₂ i.r₂) (outsideSigma2_le gffBase.gff _ _ _ _)
    (indep_localSigma_sup_outsideSigma2 gffBase.gff i.r₁_pos i.r₂_pos i.dist_le)
    (measurable_g3Y γ i) (measurable_g3a γ g i) (measurable_g3F γ i) (g3F_le_one γ i)
    (fun u o ho => setLIntegral_rcdTail (outsideSigma2_le gffBase.gff _ _ _ _)
      (measurable_g3Y' γ i) u ho) hfm
  rw [← e]
  refine lintegral_congr fun ω => lintegral_congr fun ℓ => ?_
  simp only [g3D, indicator, mem_ofPred_eq, mem_Ioi, mem_Iic, g3pMass_toReal_eq (h1 ω),
    Pi.one_apply]
  by_cases ha : 0 < ℓ <;> by_cases hb : ℓ ≤ g3Y γ i ω + g3a γ g i ω <;> simp [ha, hb]

end R18
end QuantumZipper
