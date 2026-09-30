import QuantumZipper.Proofs.Thm18.G3SchemeCI
import Mathlib.Probability.Kernel.CondDistrib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): integrating out region 1 given the outside field

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71 ("even with this conditioning"): given
the field outside both half-discs, region 1 is independent of region 2. Here in the form used for
the Palm constraint `ℓ ≤ Y + c` on the `R(x)`-side (D85 update 18:30):
if `𝓛 ⫫ 𝓑 ⊔ 𝓞`, `Y` is `𝓛 ⊔ 𝓞`-measurable, `c` is `𝓞`-measurable and `G(·, u)` is a version of
`P(Y ≥ u | 𝓞)` (jointly measurable), then for `f` measurable for `(𝓑 ⊔ 𝓞) ⊗ Borel`
`∫∫ f(ω, ℓ) 1{ℓ ≤ Y ω + c ω} dℓ dP = ∫∫ f(ω, ℓ) G(ω, ℓ − c ω) dℓ dP` (`lintegral_threshold_eq`).
The version `G` is the regular conditional distribution (`condDistrib`) of `Y` given `𝓞`
(`rcdTail`). Standard conditional-expectation calculus (Kallenberg, *Foundations of Modern
Probability*, Thm 6.3–6.4); own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

section Abstract

variable {Ω : Type*} {𝓛 𝓑 𝓞 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Two measures agreeing on a sub-σ-algebra have the same integrals of its measurable functions. -/
theorem lintegral_eq_of_forall_sub (hm : 𝓞 ≤ mΩ) {μ ν : Measure Ω}
    (h : ∀ s, MeasurableSet[𝓞] s → μ s = ν s) {f : Ω → ℝ≥0∞} (hf : Measurable[𝓞] f) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν := by
  rw [← lintegral_trim hm hf, ← lintegral_trim hm hf]
  congr 1
  refine @Measure.ext Ω 𝓞 _ _ fun s hs => ?_
  rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, h s hs]

theorem integral_eq_of_forall_sub (hm : 𝓞 ≤ mΩ) {μ ν : Measure Ω}
    (h : ∀ s, MeasurableSet[𝓞] s → μ s = ν s) {f : Ω → ℝ} (hf : StronglyMeasurable[𝓞] f) :
    ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  rw [integral_trim hm hf, integral_trim hm hf]
  congr 1
  refine @Measure.ext Ω 𝓞 _ _ fun s hs => ?_
  rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, h s hs]

/-- **Set form.** For `F ∈ 𝓑 ⊔ 𝓞` and `H ∈ 𝓛 ⊔ 𝓞` with `𝓛 ⫫ 𝓑 ⊔ 𝓞`, and `k` an `𝓞`-version of
`P(H | 𝓞)`: `P(F ∩ H) = ∫_F k`. -/
theorem measure_inter_eq_setLIntegral (h𝓛 : 𝓛 ≤ mΩ) (h𝓑 : 𝓑 ≤ mΩ) (h𝓞 : 𝓞 ≤ mΩ)
    (hind : Indep 𝓛 (𝓑 ⊔ 𝓞) P) {H : Set Ω} (hH : MeasurableSet[𝓛 ⊔ 𝓞] H)
    {k : Ω → ℝ≥0∞} (hk : Measurable[𝓞] k) (hk1 : ∀ ω, k ω ≤ 1)
    (hkH : ∀ o, MeasurableSet[𝓞] o → ∫⁻ x in o, k x ∂P = P (o ∩ H))
    {F : Set Ω} (hF : MeasurableSet[𝓑 ⊔ 𝓞] F) : P (F ∩ H) = ∫⁻ x in F, k x ∂P := by
  have hH0 : MeasurableSet H := sup_le h𝓛 h𝓞 H hH
  have hF0 : MeasurableSet F := sup_le h𝓑 h𝓞 F hF
  have hk0 : Measurable k := hk.mono h𝓞 le_rfl
  have hkt : ∀ ω, k ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top ENNReal.one_ne_top (hk1 ω)
  set f : Ω → ℝ := F.indicator (fun _ => (1 : ℝ)) with hf
  have hfi : Integrable f P := (integrable_const (1 : ℝ)).indicator hF0
  set g : Ω → ℝ := P[f | 𝓞] with hg
  set kr : Ω → ℝ := fun ω => (k ω).toReal with hkr
  have hkr_sm : StronglyMeasurable[𝓞] kr := (hk.ennreal_toReal).stronglyMeasurable
  have hkr_b : ∀ ω, ‖kr ω‖ ≤ 1 := fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hk1 ω)
  -- step 1: `∫_H f = ∫_H g`
  have e1 : ∫ x in H, f x ∂P = ∫ x in H, g x ∂P := by
    rw [← setIntegral_condExp (sup_le h𝓛 h𝓞) hfi hH]
    exact setIntegral_congr_ae hH0 ((condExp_indicator_sup_eq h𝓛 h𝓑 h𝓞 hind hF).mono
      fun x hx _ => hx)
  -- step 2: `∫_H g = ∫ k g`
  have e2 : ∫ x in H, g x ∂P = ∫ x, kr x * g x ∂P := by
    rw [integral_eq_of_forall_sub h𝓞 (ν := P.withDensity k) (fun s hs => by
      rw [Measure.restrict_apply (h𝓞 s hs), withDensity_apply _ (h𝓞 s hs), hkH s hs])
      stronglyMeasurable_condExp, integral_withDensity_eq_integral_toReal_smul hk0
      (Eventually.of_forall fun x => (hkt x).lt_top)]
    rfl
  -- step 3: `∫ k g = ∫ k f`
  have e3 : ∫ x, kr x * g x ∂P = ∫ x, kr x * f x ∂P := by
    have hkfi : Integrable (fun x => kr x * f x) P :=
      hfi.bdd_mul (hkr_sm.mono h𝓞).aestronglyMeasurable (Eventually.of_forall hkr_b)
    rw [← integral_condExp h𝓞 (f := fun x => kr x * f x)]
    refine integral_congr_ae ?_
    exact (condExp_mul_of_stronglyMeasurable_left hkr_sm hkfi hfi).symm
  -- step 4: back to measures
  have e4 : ∫ x, kr x * f x ∂P = (∫⁻ x in F, k x ∂P).toReal := by
    rw [integral_toReal (hk0.aemeasurable.restrict) (ae_of_all _ fun x => (hkt x).lt_top) |>.symm]
    rw [← integral_indicator hF0]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ F
    · simp [hf, hkr, hx]
    · simp [hf, hkr, hx]
  have e0 : ∫ x in H, f x ∂P = P.real (F ∩ H) := by
    rw [hf, integral_indicator_const _ hF0, measureReal_restrict_apply hF0, smul_eq_mul, mul_one]
  have hfin : ∫⁻ x in F, k x ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top P F) (by
      calc ∫⁻ x in F, k x ∂P ≤ ∫⁻ _ in F, 1 ∂P := lintegral_mono hk1
        _ = P F := by rw [setLIntegral_const, one_mul])
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top P _) hfin, ← measureReal_def,
    ← e0, e1, e2, e3, e4]

/-- **Function form.** -/
theorem lintegral_restrict_eq_mul (h𝓛 : 𝓛 ≤ mΩ) (h𝓑 : 𝓑 ≤ mΩ) (h𝓞 : 𝓞 ≤ mΩ)
    (hind : Indep 𝓛 (𝓑 ⊔ 𝓞) P) {H : Set Ω} (hH : MeasurableSet[𝓛 ⊔ 𝓞] H)
    {k : Ω → ℝ≥0∞} (hk : Measurable[𝓞] k) (hk1 : ∀ ω, k ω ≤ 1)
    (hkH : ∀ o, MeasurableSet[𝓞] o → ∫⁻ x in o, k x ∂P = P (o ∩ H))
    {f : Ω → ℝ≥0∞} (hf : Measurable[𝓑 ⊔ 𝓞] f) :
    ∫⁻ x in H, f x ∂P = ∫⁻ x, f x * k x ∂P := by
  have h𝓜 : 𝓑 ⊔ 𝓞 ≤ mΩ := sup_le h𝓑 h𝓞
  rw [lintegral_eq_of_forall_sub h𝓜 (ν := P.withDensity k) (fun s hs => by
      rw [Measure.restrict_apply (h𝓜 s hs), withDensity_apply _ (h𝓜 s hs)]
      exact measure_inter_eq_setLIntegral h𝓛 h𝓑 h𝓞 hind hH hk hk1 hkH hs) hf,
    lintegral_withDensity_eq_lintegral_mul _ (hk.mono h𝓞 le_rfl) (hf.mono h𝓜 le_rfl)]
  simp_rw [Pi.mul_apply, mul_comm]

/-- **Integrating out the threshold.** -/
theorem lintegral_threshold_eq (h𝓛 : 𝓛 ≤ mΩ) (h𝓑 : 𝓑 ≤ mΩ) (h𝓞 : 𝓞 ≤ mΩ)
    (hind : Indep 𝓛 (𝓑 ⊔ 𝓞) P) {Y c : Ω → ℝ} (hY : Measurable[𝓛 ⊔ 𝓞] Y)
    (hc : Measurable[𝓞] c) {G : Ω → ℝ → ℝ≥0∞}
    (hG : Measurable[@Prod.instMeasurableSpace Ω ℝ 𝓞 _] fun p : Ω × ℝ => G p.1 p.2)
    (hG1 : ∀ ω u, G ω u ≤ 1)
    (hGH : ∀ u o, MeasurableSet[𝓞] o → ∫⁻ x in o, G x u ∂P = P (o ∩ {x | u ≤ Y x}))
    {f : Ω × ℝ → ℝ≥0∞} (hf : Measurable[@Prod.instMeasurableSpace Ω ℝ (𝓑 ⊔ 𝓞) _] f) :
    ∫⁻ ω, ∫⁻ ℓ, f (ω, ℓ) * (Iic (Y ω + c ω)).indicator 1 ℓ ∂volume ∂P =
      ∫⁻ ω, ∫⁻ ℓ, f (ω, ℓ) * G ω (ℓ - c ω) ∂volume ∂P := by
  have h𝓜 : 𝓑 ⊔ 𝓞 ≤ mΩ := sup_le h𝓑 h𝓞
  -- the shifted integrand
  set f' : Ω × ℝ → ℝ≥0∞ := fun p => f (p.1, p.2 + c p.1) with hf'
  have hsh : @Measurable _ _ (@Prod.instMeasurableSpace Ω ℝ (𝓑 ⊔ 𝓞) _)
      (@Prod.instMeasurableSpace Ω ℝ (𝓑 ⊔ 𝓞) _) fun p : Ω × ℝ => (p.1, p.2 + c p.1) := by
    refine Measurable.prodMk (m := @Prod.instMeasurableSpace Ω ℝ (𝓑 ⊔ 𝓞) _)
      (@measurable_fst Ω ℝ (𝓑 ⊔ 𝓞) _) ?_
    exact (@measurable_snd Ω ℝ (𝓑 ⊔ 𝓞) _).add
      ((hc.mono le_sup_right le_rfl).comp (@measurable_fst Ω ℝ (𝓑 ⊔ 𝓞) _))
  have hf'm : Measurable[@Prod.instMeasurableSpace Ω ℝ (𝓑 ⊔ 𝓞) _] f' := hf.comp hsh
  have hprod : @Prod.instMeasurableSpace Ω ℝ (𝓑 ⊔ 𝓞) _ ≤ @Prod.instMeasurableSpace Ω ℝ mΩ _ :=
    sup_le_sup (MeasurableSpace.comap_mono h𝓜) le_rfl
  have hprodO : @Prod.instMeasurableSpace Ω ℝ 𝓞 _ ≤ @Prod.instMeasurableSpace Ω ℝ mΩ _ :=
    sup_le_sup (MeasurableSpace.comap_mono h𝓞) le_rfl
  have hY0 : Measurable Y := hY.mono (sup_le h𝓛 h𝓞) le_rfl
  -- shift each inner integral
  have sL : ∀ ω, ∫⁻ ℓ, f (ω, ℓ) * (Iic (Y ω + c ω)).indicator 1 ℓ ∂volume =
      ∫⁻ u, f' (ω, u) * (Iic (Y ω)).indicator 1 u ∂volume := fun ω => by
    rw [← lintegral_add_right_eq_self (μ := volume) _ (c ω)]
    refine lintegral_congr fun u => ?_
    simp only [hf', indicator, mem_Iic, add_le_add_iff_right, Pi.one_apply]
  have sR : ∀ ω, ∫⁻ ℓ, f (ω, ℓ) * G ω (ℓ - c ω) ∂volume = ∫⁻ u, f' (ω, u) * G ω u ∂volume :=
    fun ω => by
      rw [← lintegral_add_right_eq_self (μ := volume) _ (c ω)]
      refine lintegral_congr fun u => ?_
      simp only [hf', add_sub_cancel_right]
  simp_rw [sL, sR]
  -- swap and integrate out for each `u`
  have mL : Measurable fun p : Ω × ℝ => f' p * (Iic (Y p.1)).indicator 1 p.2 := by
    refine (hf'm.mono hprod le_rfl).mul (Measurable.indicator measurable_const ?_)
    exact measurableSet_le measurable_snd (hY0.comp measurable_fst)
  have mR : Measurable fun p : Ω × ℝ => f' p * G p.1 p.2 :=
    (hf'm.mono hprod le_rfl).mul (hG.mono hprodO le_rfl)
  have sw1 := lintegral_lintegral_swap (μ := P) (ν := volume)
    (f := fun ω u => f' (ω, u) * (Iic (Y ω)).indicator 1 u) mL.aemeasurable
  have sw2 := lintegral_lintegral_swap (μ := P) (ν := volume)
    (f := fun ω u => f' (ω, u) * G ω u) mR.aemeasurable
  rw [sw1, sw2]
  refine lintegral_congr fun u => ?_
  have hHu : MeasurableSet[𝓛 ⊔ 𝓞] {x | u ≤ Y x} := measurableSet_le measurable_const hY
  have hku : Measurable[𝓞] fun x => G x u :=
    hG.comp (Measurable.prodMk (m := 𝓞) (@measurable_id Ω 𝓞) measurable_const)
  have hfu : Measurable[𝓑 ⊔ 𝓞] fun x => f' (x, u) :=
    hf'm.comp (Measurable.prodMk (m := 𝓑 ⊔ 𝓞) (@measurable_id Ω (𝓑 ⊔ 𝓞))
      measurable_const)
  have e := lintegral_restrict_eq_mul h𝓛 h𝓑 h𝓞 hind hHu hku (fun ω => hG1 ω u)
    (fun o ho => hGH u o ho) hfu
  rw [← e, ← lintegral_indicator (sup_le h𝓛 h𝓞 _ hHu)]
  refine lintegral_congr fun x => ?_
  by_cases hx : u ≤ Y x
  · simp [indicator, hx]
  · simp [indicator, hx]

end Abstract

section Rcd

/-- Upper tails of a finite kernel are jointly measurable. -/
theorem measurable_kernel_Ici {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ)
    [IsFiniteKernel κ] : Measurable fun p : Ω × ℝ => κ p.1 (Ici p.2) :=
  (κ.comap Prod.fst measurable_fst).measurable_kernel_prodMk_left
    (t := {p : (Ω × ℝ) × ℝ | p.1.2 ≤ p.2})
    (measurableSet_le (measurable_snd.comp measurable_fst) measurable_snd)

variable {Ω : Type*} (𝓞 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P]

/-- The regular conditional distribution of `Y` given the sub-σ-algebra `𝓞`. -/
def rcdK (Y : Ω → ℝ) : @Kernel Ω ℝ 𝓞 _ :=
  @condDistrib Ω Ω ℝ _ _ _ mΩ 𝓞 Y id P _

/-- The conditional tail `P(Y ≥ u | 𝓞)(ω)`. -/
def rcdTail (Y : Ω → ℝ) (ω : Ω) (u : ℝ) : ℝ≥0∞ :=
  rcdK 𝓞 P Y ω (Ici u)

variable {𝓞 P}

theorem isMarkovKernel_rcdK (Y : Ω → ℝ) : @IsMarkovKernel Ω ℝ 𝓞 _ (rcdK 𝓞 P Y) := by
  unfold rcdK; infer_instance

theorem rcdTail_le_one (Y : Ω → ℝ) (ω : Ω) (u : ℝ) : rcdTail 𝓞 P Y ω u ≤ 1 := by
  have := @IsMarkovKernel.isProbabilityMeasure Ω ℝ 𝓞 _ _ (isMarkovKernel_rcdK (P := P) Y) ω
  exact prob_le_one

theorem measurable_rcdTail (Y : Ω → ℝ) :
    Measurable[@Prod.instMeasurableSpace Ω ℝ 𝓞 _] fun p : Ω × ℝ => rcdTail 𝓞 P Y p.1 p.2 :=
  have := isMarkovKernel_rcdK (𝓞 := 𝓞) (P := P) Y
  @measurable_kernel_Ici Ω 𝓞 (rcdK 𝓞 P Y) inferInstance

theorem setLIntegral_rcdTail (h𝓞 : 𝓞 ≤ mΩ) {Y : Ω → ℝ}
    (hY : Measurable Y) (u : ℝ) {o : Set Ω} (ho : MeasurableSet[𝓞] o) :
    ∫⁻ x in o, rcdTail 𝓞 P Y x u ∂P = P (o ∩ {x | u ≤ Y x}) := by
  have hX : @Measurable Ω Ω mΩ 𝓞 id := measurable_id'' h𝓞
  have ho' : MeasurableSet[𝓞.comap id] o := by rwa [MeasurableSpace.comap_id]
  exact setLIntegral_condDistrib_of_measurableSet (mβ := 𝓞) (μ := P) (X := id) (Y := Y)
    (s := Ici u) hX hY.aemeasurable measurableSet_Ici ho'

theorem rcdTail_ae_eq_condExp (h𝓞 : 𝓞 ≤ mΩ) {Y : Ω → ℝ} (hY : Measurable Y) (u : ℝ) :
    (fun x => (rcdTail 𝓞 P Y x u).toReal) =ᵐ[P]
      P[{x | u ≤ Y x}.indicator (fun _ => (1 : ℝ)) | 𝓞] := by
  have hX : @Measurable Ω Ω mΩ 𝓞 id := measurable_id'' h𝓞
  have h := condDistrib_ae_eq_condExp (mβ := 𝓞) (μ := P) (X := id) (Y := Y) (s := Ici u) hX hY
    measurableSet_Ici
  rw [MeasurableSpace.comap_id] at h
  exact h

end Rcd

end R18
end QuantumZipper
