/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA3Noise
import InteractingSLE.Spec.Sec7.LocalExtA3Gauss

/-!
# The local comparison of Aux. lemma 55: the variance identity `E X_t² = E ∫₀^{t∧S} A²`

Packet PROVE-LOCEXT-A3, item 2 (e). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L163–L182, p. 248): "The
Loewner Green identity gives `∫₀^{t∧S} a_s² ds = ‖f‖²_∇ − G_{ℍ∖K_{t∧S}}(v, v)`."

The field side gives the conditional law of the pairing `(h, v)` at every driving stop `τ ≤ S` (`condExp_cexp_srcPair`):
Gaussian with mean `(𝔥_τ, v)` and variance `E_τ(v)`. Hence (with `c = (𝔥₀, v)`, `‖f‖²_∇ = srcNorm`):

* at `τ = 0` the pairing is Gaussian `N(c, ‖f‖²_∇)` (`map_srcPair_eq_gaussianReal`), so `E((h, v) − c)² = ‖f‖²_∇`;
* at `τ = t ∧ S`, `E[((h, v) − c)² | 𝓖_τ] = E_τ(v) + ((𝔥_τ, v) − c)²` (`ae_condExp_sq_sub_of_condGauss`, through the
  regular conditional distribution), and `E_τ(v) = ‖f‖²_∇ − ∫₀^{t∧S} A²`;
* **`integral_meanStop_sub_sq_eq`**: `E X_t² = E ∫₀ᵗ θ²` for `X_t = ∫ 𝔥_{t∧S} v − c` and `θ = srcTheta`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec2 Girsanov

/-! ### Second moments of conditionally Gaussian variables -/

section Abstract

/-- `∫ (x − k)² dN(μ, v) = v + (μ − k)²`. -/
theorem integral_sq_sub_gaussianReal (μ k : ℝ) (v : ℝ≥0) :
    ∫ x, (x - k) ^ 2 ∂gaussianReal μ v = v + (μ - k) ^ 2 := by
  have h1 : ∫ x, (x - μ) ^ 2 ∂gaussianReal μ v = v := by
    have := variance_fun_id_gaussianReal (μ := μ) (v := v)
    rw [variance_eq_integral measurable_id'.aemeasurable] at this
    simpa only [integral_id_gaussianReal] using this
  have hI1 : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 1).integrable (by norm_num)
  have hI2 : Integrable (fun x : ℝ => (x - μ) ^ 2) (gaussianReal μ v) := by
    have h2 : MemLp (fun x : ℝ => x - μ) 2 (gaussianReal μ v) :=
      (memLp_id_gaussianReal' (μ := μ) (v := v) 2 (by norm_num)).sub (memLp_const μ)
    exact h2.integrable_sq
  have e : (fun x : ℝ => (x - k) ^ 2) = fun x => (x - μ) ^ 2 + (2 * (μ - k) * (x - μ) + (μ - k) ^ 2) := by
    funext x; ring
  have hI3 : Integrable (fun x : ℝ => 2 * (μ - k) * (x - μ)) (gaussianReal μ v) :=
    (hI1.sub (integrable_const μ)).const_mul _
  have hI4 : Integrable (fun x : ℝ => 2 * (μ - k) * (x - μ) + (μ - k) ^ 2) (gaussianReal μ v) :=
    hI3.add (integrable_const _)
  rw [e, integral_add hI2 hI4, integral_add hI3 (integrable_const _), h1,
    integral_const_mul, integral_sub hI1 (integrable_const μ), integral_id_gaussianReal]
  simp

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Real conditional expectations given `m` are integrals against `condLaw`. -/
theorem condExp_ae_eq_integral_condLaw_real [IsFiniteMeasure P] (hm : m ≤ mΩ) {Y : Ω → ℝ × ℝ}
    (hY : Measurable Y) {f : ℝ × ℝ → ℝ} (hf : StronglyMeasurable f)
    (hint : Integrable (fun ω => f (Y ω)) P) :
    P[fun ω => f (Y ω) | m] =ᵐ[P] fun ω => ∫ y, f y ∂condLaw m Y P ω := by
  have h := condExp_ae_eq_integral_condDistrib (mβ := m) (X := (id : Ω → Ω)) (measurable_id'' hm)
    hY.aemeasurable hf hint
  rwa [MeasurableSpace.comap_id] at h

/-- **A variable with a Gaussian characteristic function is Gaussian.** -/
theorem map_eq_gaussianReal_of_charFun [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) {μ q : ℝ}
    (hc : ∀ c : ℝ, ∫ ω, Complex.exp (Complex.I * ((c * Y ω : ℝ) : ℂ)) ∂P = cfVal (c * μ) (c ^ 2 * q)) :
    0 ≤ q ∧ P.map Y = gaussianReal μ q.toNNReal := by
  have hY' : Measurable fun ω => (Y ω, (0 : ℝ)) := hY.prodMk measurable_const
  have : IsProbabilityMeasure (P.map fun ω => (Y ω, (0 : ℝ))) := (Measure.isProbabilityMeasure_map_iff hY'.aemeasurable).2 inferInstance
  have hν : ∀ a b : ℝ, ∫ y, Complex.exp (Complex.I * ((a * y.1 + b * y.2 : ℝ) : ℂ)) ∂(P.map fun ω => (Y ω, (0 : ℝ))) =
      cfVal (a * μ + b * 0) (a ^ 2 * q + 2 * a * b * 0 + b ^ 2 * 0) := fun a b => by
    rw [integral_map hY'.aemeasurable (by fun_prop)]
    simp only [mul_zero, add_zero]
    rw [← hc a]
  obtain ⟨hq, hmap⟩ := exists_map_eq_gaussianReal hν 1 0
  simp only [one_pow, one_mul, mul_zero, zero_mul, add_zero] at hq hmap
  refine ⟨hq, ?_⟩
  rw [Measure.map_map (by fun_prop) hY'] at hmap
  convert hmap using 2
  funext ω
  simp

/-- **The conditional second moment of a conditionally Gaussian variable**: if
`E[e^{icY} | m] = exp(icμ − c²q/2)` almost surely for every real `c`, and `(Y − k)²` is integrable, then
`E[(Y − k)² | m] = q + (μ − k)²` almost surely. -/
theorem ae_condExp_sq_sub_of_condGauss [IsProbabilityMeasure P] (hm : m ≤ mΩ) {Y : Ω → ℝ} (hY : Measurable Y)
    {μ q : Ω → ℝ}
    (hc : ∀ c : ℝ, P[fun ω => Complex.exp (Complex.I * ((c * Y ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => cfVal (c * μ ω) (c ^ 2 * q ω)) (k : ℝ)
    (hint : Integrable (fun ω => (Y ω - k) ^ 2) P) :
    P[fun ω => (Y ω - k) ^ 2 | m] =ᵐ[P] fun ω => q ω + (μ ω - k) ^ 2 := by
  set Y' : Ω → ℝ × ℝ := fun ω => (Y ω, 0) with hY'def
  have hY' : Measurable Y' := hY.prodMk measurable_const
  have h1 : ∀ p : ℚ × ℚ,
      P[fun ω => Complex.exp (Complex.I * (((p.1 : ℝ) * (Y' ω).1 + (p.2 : ℝ) * (Y' ω).2 : ℝ) : ℂ)) | m] =ᵐ[P]
        fun ω => ∫ y, Complex.exp (Complex.I * (((p.1 : ℝ) * y.1 + (p.2 : ℝ) * y.2 : ℝ) : ℂ)) ∂condLaw m Y' P ω :=
    fun p => by
      have hcont : Continuous fun y : ℝ × ℝ =>
          Complex.exp (Complex.I * (((p.1 : ℝ) * y.1 + (p.2 : ℝ) * y.2 : ℝ) : ℂ)) := by fun_prop
      refine condExp_ae_eq_integral_condLaw hm hY' hcont.stronglyMeasurable ?_
      exact Integrable.of_bound (hcont.measurable.comp hY').aestronglyMeasurable 1
        (ae_of_all _ fun ω => (norm_cexp_I_mul _).le)
  have h2 : P[fun ω => (Y ω - k) ^ 2 | m] =ᵐ[P] fun ω => ∫ y, (y.1 - k) ^ 2 ∂condLaw m Y' P ω :=
    condExp_ae_eq_integral_condLaw_real hm hY' (by fun_prop : Continuous fun y : ℝ × ℝ => (y.1 - k) ^ 2).stronglyMeasurable
      hint
  filter_upwards [ae_all_iff.2 h1, h2, ae_all_iff.2 fun p : ℚ × ℚ => hc (p.1 : ℝ)] with ω e1 e2 e3
  rw [e2]
  have hν : ∀ a b : ℚ, ∫ y, Complex.exp (Complex.I * (((a : ℝ) * y.1 + (b : ℝ) * y.2 : ℝ) : ℂ)) ∂condLaw m Y' P ω =
      cfVal ((a : ℝ) * μ ω + (b : ℝ) * 0) ((a : ℝ) ^ 2 * q ω + 2 * (a : ℝ) * (b : ℝ) * 0 + (b : ℝ) ^ 2 * 0) :=
    fun a b => by
      rw [← e1 (a, b)]
      simp only [hY'def, mul_zero, add_zero]
      exact e3 (a, b)
  obtain ⟨hq, hmap⟩ := exists_map_eq_gaussianReal (integral_cexp_pair_eq_of_rat hν) 1 0
  have hq' : 0 ≤ q ω := by simpa using hq
  have hL : Measurable fun y : ℝ × ℝ => 1 * y.1 + 0 * y.2 := by fun_prop
  have e : ∫ y, (y.1 - k) ^ 2 ∂condLaw m Y' P ω =
      ∫ x, (x - k) ^ 2 ∂(condLaw m Y' P ω).map fun y : ℝ × ℝ => 1 * y.1 + 0 * y.2 := by
    rw [integral_map hL.aemeasurable (by fun_prop)]
    simp
  rw [e, hmap, integral_sq_sub_gaussianReal]
  simp only [one_pow, one_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  rw [Real.coe_toNNReal _ hq']

end Abstract

/-! ### The variance identity -/

section Main

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- At time `0` the tested mean of the source is `(𝔥₀, v)` along a good path. -/
theorem srcMeanAt_zero_of_isGoodPath {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    srcMeanAt κ xL xR ρL ρR r W VL VR 0 ω = srcCentre κ xL xR ρL ρR r := by
  have h1 := srcMart_zero_of_isGoodPath hg hF hr (κ := κ) (r := r)
  rw [srcMart, NNReal.coe_zero, intervalIntegral.integral_same, zero_div, sub_zero, Real.exp_eq_one_iff,
    neg_eq_zero, sub_eq_zero] at h1
  exact h1

/-- **The pairing with the source is Gaussian** `N((𝔥₀, v), ‖f‖²_∇)`. -/
theorem map_srcPair_eq_gaussianReal (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    0 ≤ srcNorm κ xL xR ρL ρR r ∧ P.map (fun ω => srcPair κ ρL ρR hF hr (h ω)) =
      gaussianReal (srcCentre κ xL xR ρL ρR r) (srcNorm κ xL xR ρL ρR r).toNNReal := by
  have hP : IsProbabilityMeasure P := hC.1.1.isProbabilityMeasure'
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hYm : Measurable fun ω => srcPair κ ρL ρR hF hr (h ω) := (measurable_srcPair hF hr).comp hC.2.1
  refine map_eq_gaussianReal_of_charFun hYm fun c => ?_
  have hτ0 : IsStoppingTime (drivingFiltration P hX) fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have hcf := condExp_cexp_srcPair hκ hC hF hr hseed hX hτ0 (ae_of_all _ fun ω => by simp) c
  rw [← integral_condExp hτ0.measurableSpace_le, integral_congr_ae hcf]
  have hc : (fun ω => cfVal (c * srcMeanAt κ xL xR ρL ρR r W VL VR (((0 : ℝ≥0) : WithTop ℝ≥0).untopD 0) ω)
      (c ^ 2 * srcEnergyAt κ xL xR ρL ρR r W (((0 : ℝ≥0) : WithTop ℝ≥0).untopD 0) ω)) =ᵐ[P]
      fun _ => cfVal (c * srcCentre κ xL xR ρL ρR r) (c ^ 2 * srcNorm κ xL xR ρL ρR r) := by
    filter_upwards [ae_isGoodPath hC.1 hκ] with ω hg
    rw [WithTop.untopD_coe, srcMeanAt_zero_of_isGoodPath hg hF hr]
    have hE := loewnerGreenEnergy_vSrc_eq_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) hg.1 hg.2 hF hr hseed
      (t := 0) (by simp)
    simp only [srcEnergyAt]
    rw [show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl, hE]
    simp
  rw [integral_congr_ae hc]
  simp

/-- **The variance identity** `E X_t² = E ∫₀ᵗ θ²` for `X_t = ∫ 𝔥_{t∧S} v − (𝔥₀, v)` and `θ = srcTheta`. -/
theorem integral_meanStop_sub_sq_eq (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω) (t : ℝ≥0) :
    ∫ ω, (meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω - srcCentre κ xL xR ρL ρR r) ^ 2 ∂P =
      ∫ ω, quadInt (srcTheta κ xL xR ρL ρR r W VL VR ζ G) t ω ∂P := by
  have hE := hC.1
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨hX, hker⟩ := hC.2.2.2
  have hGp : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := fun ω hω => (hG ω hω).1
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set c₀ := srcCentre κ xL xR ρL ρR r with hc₀
  set Nn := srcNorm κ xL xR ρL ρR r with hNn
  have hYm : Measurable fun ω => srcPair κ ρL ρR hF hr (h ω) := (measurable_srcPair hF hr).comp hC.2.1
  -- 1. the unconditional law
  obtain ⟨hN0, hlaw⟩ := map_srcPair_eq_gaussianReal hκ hC hF hr hseed
  have hY2 : Integrable (fun ω => (srcPair κ ρL ρR hF hr (h ω) - c₀) ^ 2) P := by
    have h1 : Integrable (fun x : ℝ => (x - c₀) ^ 2) (P.map fun ω => srcPair κ ρL ρR hF hr (h ω)) := by
      rw [hlaw]
      exact ((memLp_id_gaussianReal' (μ := c₀) (v := Nn.toNNReal) 2 (by norm_num)).sub
        (memLp_const c₀)).integrable_sq
    exact (integrable_map_measure (by fun_prop) hYm.aemeasurable).1 h1
  have hvar0 : ∫ ω, (srcPair κ ρL ρR hF hr (h ω) - c₀) ^ 2 ∂P = Nn := by
    have h1 := integral_map (μ := P) hYm.aemeasurable
      (f := fun x : ℝ => (x - c₀) ^ 2) (by fun_prop : Continuous fun x : ℝ => (x - c₀) ^ 2).aestronglyMeasurable
    rw [← h1, hlaw, integral_sq_sub_gaussianReal, Real.coe_toNNReal _ hN0, sub_self, zero_pow two_ne_zero,
      add_zero]
  -- 2. the conditional law at `τ = S ∧ t`
  have hτ : IsStoppingTime (drivingFiltration P hX) fun ω => min (capStop r G ζ W ω) (t : WithTop ℝ≥0) :=
    (isStoppingTime_capStop hX hGm hGc hGp r).min_const t
  have hτS : ∀ᵐ ω ∂P, min (capStop r G ζ W ω) (t : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    filter_upwards [hGae] with ω hω
    rw [capStop_eq_localStop hGp hF hr hseed hω, localStop_of_mem hω]
    exact min_le_left _ _
  have huntop : ∀ ω ∈ G, (min (capStop r G ζ W ω) (t : WithTop ℝ≥0)).untopD 0 = min t (stopTime r G ζ W ω) :=
    fun ω hω => by
      rw [← coe_capTime, capTime_eq_stopTime hGp hF hr hseed hω, ← WithTop.coe_min, WithTop.untopD_coe, min_comm]
  have hcond := ae_condExp_sq_sub_of_condGauss hτ.measurableSpace_le hYm
    (fun c => condExp_cexp_srcPair hκ hC hF hr hseed hX hτ hτS c) c₀ hY2
  obtain ⟨hθp, hθb, -⟩ := (Ito.isIntegratedSLEEvolution_usualAugmentation hE).isSLEEvolutionUpTo.weightDrift_props
    (seedWtL xL ρL) (seedWtR xR ρR) (measurableSet_le_capTime hE hGm hGc hGp)
    (capTime_le_zeta (r := r) (G := G) (ζ := ζ) (W := W)) (show (0 : ℝ) < 7 * r by have := hr.1; positivity)
  have hmean := martingale_meanStop_vSrc hκ hE hF hr hseed hGm hGc hG
  have h2 : ∫ ω, (srcPair κ ρL ρR hF hr (h ω) - c₀) ^ 2 ∂P =
      ∫ ω, (Nn - quadInt (srcTheta κ xL xR ρL ρR r W VL VR ζ G) t ω +
        (meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω - c₀) ^ 2) ∂P := by
    rw [← integral_condExp hτ.measurableSpace_le]
    refine integral_congr_ae ?_
    filter_upwards [hcond, hGae] with ω h1 hω
    rw [h1]
    simp only [huntop ω hω]
    have hle : ((min t (stopTime r G ζ W ω) : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
      rw [← coe_stopTime_of_mem hω]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
    have hq := loewnerGreenEnergy_vSrc_eq_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) (hG ω hω).1.1 (hG ω hω).1.2
      hF hr hseed hle
    have hqi := quadInt_srcTheta_eq hGp hF hr hseed hθp hθb hω t
    simp only [srcEnergyAt]
    rw [show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl, hq, hqi]
    simp only [meanStop, hω, ↓reduceIte]
    rfl
  -- 3. conclusion
  have hQm : ∀ s, Measurable (quadInt (srcTheta κ xL xR ρL ρR r W VL VR ζ G) s) := fun s =>
    ((stronglyMeasurable_integral_comp hθp (measurable_id.pow_const 2) s).mono
      ((usualAugmentation 𝓕 P).le s)).measurable
  set C := |1 / Real.sqrt κ| * ((∑ j, |weightDiff ρL (seedWtL xL ρL) ρR (seedWtR xR ρR) j|) * (7 * r)⁻¹) with hC'
  have hQi : Integrable (quadInt (srcTheta κ xL xR ρL ρR r W VL VR ζ G) t) P := by
    refine Integrable.of_bound (hQm t).aestronglyMeasurable (C ^ 2 * t) (ae_of_all _ fun ω => ?_)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
      (f := fun u : ℝ => srcTheta κ xL xR ρL ρR r W VL VR ζ G u.toNNReal ω ^ 2) (C := C ^ 2) fun u _ => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hθb _ _) 2
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.coe_nonneg] at this
  have hMm : Measurable fun ω => (meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω - c₀) ^ 2 :=
    ((((hmean.1 t).mono ((usualAugmentation 𝓕 P).le t)).measurable).sub_const _).pow_const 2
  have hMi : Integrable (fun ω => (meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω - c₀) ^ 2) P := by
    refine Integrable.of_bound hMm.aestronglyMeasurable
      ((meanSrcBound κ ρL ρR r * (∫ z, |vSrc κ xL xR ρL ρR r z|) + |c₀|) ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
      (add_le_add (abs_meanStop_vSrc_le hκ hF hr hseed hG t ω) le_rfl)) 2
  have hNQ : Integrable (fun ω => Nn - quadInt (srcTheta κ xL xR ρL ρR r W VL VR ζ G) t ω) P :=
    (integrable_const Nn).sub hQi
  rw [hvar0, integral_add hNQ hMi, integral_sub (integrable_const Nn) hQi] at h2
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h2
  linarith

end Main

end LocalExt

end InteractingSLE
