import QuantumZipper.Proofs.Zipper.UnifUCE2Mix
import QuantumZipper.Proofs.Zipper.UnifUC1RadBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-E2 (decision D33), step 2: the strip form of the mixture bound and `ρ = 0`

* `energy_mixFc_le_strip`: the mixture bound of `UnifUCE2Mix.energy_mixFc_le` in the form used for
  the time modulus: the per-`z` energy is bounded by `Kb` above the strip `{Im z < τ}` (where the
  stability estimate RSTAB applies) and by the crude bound `Ks` inside it. The strip is paid for
  by its `A`-measure, `E ≤ (√Kb + √Ks · A{Im z < τ})²`.
* `revMap_map_eq_nuT`: `(fc(w,r)).map (revMap (vrev W t) t) = νT W w r t` (the two forms of the
  pushed circle, `νT` using `fwdMapInv W t`, which agrees with `revMap (vrev W t) t` on `H`).
* `energyParZero_le`: **the time modulus at `ρ = 0`**: `μ_{p,0} = νT W d 2^{-k} (u+s)`, so the
  JointMod time modulus `abs_kernelCov2_νT_time_unif` gives
  `|E(μ_{p,0} − μ_{p',0})| ≤ C · dist(p,p')^{a/12}` for Hölder drivers — uniformly in `p, p'`.

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1 (through the JointMod time modulus). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint GFFExist B2

variable {W : ℝ → ℝ}

/-- `(fc(w,r)).map (revMap (vrev W t) t) = νT W w r t` for `t ≥ 0`, `r > 0`. -/
theorem revMap_map_eq_nuT (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {w : ℂ}
    {r : ℝ} (hr : 0 < r) : (foldedCircle w r).map (revMap (vrev W t) t) = νT W w r t := by
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr] with z hz
  exact (B2.fwdMapInv_eq_revMap_vrev hW hW0 ht hz).symm

/-! ## The mixture bound with a strip cut -/

theorem energy_mixFc_le_strip {A : Measure ℂ} [IsProbabilityMeasure A] {w w' : ℂ → ℂ}
    (hw : Measurable w) (hw' : Measurable w') {ψ ψ' : ℂ → ℂ} (hψ : Measurable ψ)
    (hψ' : Measurable ψ') {ρ ρ' α C B : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hL : ∀ᵐ z ∂A, GoodM ((foldedCircle (w z) ρ).map ψ) α C B ∧
      GoodM ((foldedCircle (w' z) ρ').map ψ') α C B)
    {Kb Ks τ : ℝ} (hKb0 : 0 ≤ Kb) (hKs0 : 0 ≤ Ks)
    (hbig : ∀ᵐ z ∂A, τ ≤ z.im →
      kernelCov2 neumannH (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ'))
        (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ')) ≤ Kb)
    (hsmall : ∀ᵐ z ∂A, z.im < τ →
      kernelCov2 neumannH (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ'))
        (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ')) ≤ Ks) :
    kernelCov2 neumannH ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ')
      ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ') ≤
      (Real.sqrt Kb + Real.sqrt Ks * (A {z : ℂ | z.im < τ}).toReal) ^ 2 := by
  have hset : MeasurableSet {z : ℂ | z.im < τ} :=
    (isOpen_lt Complex.continuous_im continuous_const).measurableSet
  set K : ℂ → ℝ := fun z => Kb + (if z.im < τ then Ks else 0) with hKdef
  have hK : ∀ᵐ z ∂A, kernelCov2 neumannH (((foldedCircle (w z) ρ).map ψ),
      ((foldedCircle (w' z) ρ').map ψ')) (((foldedCircle (w z) ρ).map ψ),
      ((foldedCircle (w' z) ρ').map ψ')) ≤ K z := by
    filter_upwards [hbig, hsmall] with z hb hs
    by_cases h : z.im < τ
    · simp only [hKdef]; simp only [h, ite_true]; exact le_trans (hs h) (by linarith)
    · simp only [hKdef]; simp only [h, ite_false, add_zero]; exact hb (le_of_not_gt h)
  have hmeas : Measurable fun z : ℂ => Real.sqrt (K z) :=
    Real.continuous_sqrt.measurable.comp
      (measurable_const.add (Measurable.ite hset measurable_const measurable_const))
  have hKi : Integrable (fun z : ℂ => Real.sqrt (K z)) A := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.sqrt (Kb + Ks)) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    simp only [hKdef]
    by_cases h : z.im < τ
    · simp only [h, ite_true]; linarith
    · simp only [h, ite_false, add_zero]; linarith
  have h := energy_mixFc_le hw hw' hψ hψ' hα hC hB hL hK hKi
  -- the strip is paid for by its `A`-measure
  have hpt : ∀ z : ℂ, Real.sqrt (K z) ≤ Real.sqrt Kb + Real.sqrt Ks *
      ({z : ℂ | z.im < τ}.indicator (fun _ => (1 : ℝ)) z) := by
    intro z
    simp only [hKdef]
    by_cases h : z.im < τ
    · have hmem : z ∈ {z : ℂ | z.im < τ} := h
      rw [if_pos h, Set.indicator_of_mem hmem]
      have hsq : Kb + Ks ≤ (Real.sqrt Kb + Real.sqrt Ks) ^ 2 := by
        have h1 := Real.sq_sqrt hKb0
        have h2 := Real.sq_sqrt hKs0
        nlinarith [Real.sqrt_nonneg Kb, Real.sqrt_nonneg Ks]
      refine (Real.sqrt_le_sqrt hsq).trans (le_of_eq ?_)
      rw [Real.sqrt_sq (by positivity)]; ring
    · have hmem : z ∉ {z : ℂ | z.im < τ} := h
      rw [if_neg h, add_zero, Set.indicator_of_notMem hmem, mul_zero, add_zero]
  have hint1 : Integrable (fun z : ℂ => ({z : ℂ | z.im < τ}.indicator (fun _ => (1 : ℝ)) z)) A := by
    refine Integrable.of_bound (measurable_const.indicator hset).aestronglyMeasurable 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    by_cases h : z.im < τ
    · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | z.im < τ} from h)]; norm_num
    · rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | z.im < τ} from h)]; norm_num
  have hginteg : Integrable (fun z : ℂ => Real.sqrt Kb + Real.sqrt Ks *
      ({z : ℂ | z.im < τ}.indicator (fun _ => (1 : ℝ)) z)) A :=
    (integrable_const _).add (hint1.const_mul _)
  have hmono := integral_mono hKi hginteg hpt
  have hcalc : ∫ z : ℂ, (Real.sqrt Kb + Real.sqrt Ks *
      ({z : ℂ | z.im < τ}.indicator (fun _ => (1 : ℝ)) z)) ∂A =
      Real.sqrt Kb + Real.sqrt Ks * (A {z : ℂ | z.im < τ}).toReal := by
    rw [integral_add (integrable_const _) (hint1.const_mul _), integral_const_mul,
      integral_indicator_const (1 : ℝ) hset, integral_const]
    simp [Measure.real, probReal_univ]
  have h2 : (∫ (z : ℂ), Real.sqrt (K z) ∂A) ^ 2 ≤
      (Real.sqrt Kb + Real.sqrt Ks * (A {z : ℂ | z.im < τ}).toReal) ^ 2 :=
    pow_le_pow_left₀ (integral_nonneg fun z => Real.sqrt_nonneg _)
      (hmono.trans (le_of_eq hcalc)) 2
  exact h.trans h2

/-! ## The time modulus at `ρ = 0` -/

/-- **UNIF-RC3-E2, `ρ = 0`.** For a Hölder driver, `|E(μ_{p,0} − μ_{p',0})| ≤ C·dist(p,p')^{a/12}`
on `tri T × tri T`, with `C = 2 · timeK M T 2^{-k} (‖d‖+2^{-k}+1) CH`. -/
theorem energyParZero_le (hW : Continuous W) (hW0 : W 0 = 0) {T Mw a CH : ℝ} (hT : 0 ≤ T)
    (hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) (d : ℂ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ tri T, ∀ p' ∈ tri T,
      |kernelCov2 neumannH (muUS W d k p 0, muUS W d k p' 0)
        (muUS W d k p 0, muUS W d k p' 0)| ≤ C * dist p p' ^ (a / 12) := by
  set rk := radius k with hrk
  have hrk0 : 0 < rk := radius_pos k
  have hrk1 : rk ≤ 1 := by
    rw [hrk]; exact pow_le_one₀ (by norm_num) (by norm_num)
  set R := ‖d‖ + rk + 1 with hR
  have hdR : ‖d‖ + rk ≤ R := by rw [hR]; linarith
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  set K := timeK Mw T rk R CH with hK
  have hK0 : 0 ≤ K := by
    have h1 := timeConst_nonneg (R := R) hMw0 hT hrk0
    have h2 := potC_nonneg (R := R) hMw0 hT hrk0
    have h3 : (0 : ℝ) ≤ (CH + 1) ^ (1 / 12 : ℝ) := Real.rpow_nonneg (by linarith) _
    rw [hK]; unfold timeK; positivity
  refine ⟨2 * K, by positivity, fun p hp p' hp' => ?_⟩
  have hpT : p.1 + p.2 ∈ Icc (0 : ℝ) T := ⟨add_nonneg hp.1 hp.2.1, hp.2.2⟩
  have hp'T : p'.1 + p'.2 ∈ Icc (0 : ℝ) T := ⟨add_nonneg hp'.1 hp'.2.1, hp'.2.2⟩
  have hu : p.1 + p.2 ≥ 0 := hpT.1
  have hu' : p'.1 + p'.2 ≥ 0 := hp'T.1
  rw [muUS_zero_eq hW hW0 hMw d k hp, muUS_zero_eq hW hW0 hMw d k hp',
    revMap_map_eq_nuT hW hW0 hu hrk0, revMap_map_eq_nuT hW hW0 hu' hrk0]
  refine (abs_kernelCov2_νT_time_unif hW hW0 hrk0 hMw ha ha1 hCH hH le_rfl hdR hpT hp'T).trans ?_
  set δ := dist p p' with hδ
  have hδ0 : 0 ≤ δ := dist_nonneg
  have h1 : |p.1 + p.2 - (p'.1 + p'.2)| ≤ 2 * δ := by
    have h2 : |p.1 - p'.1| ≤ δ := by
      rw [← Real.dist_eq, hδ, Prod.dist_eq]; exact le_max_left _ _
    have h3 : |p.2 - p'.2| ≤ δ := by
      rw [← Real.dist_eq, hδ, Prod.dist_eq]; exact le_max_right _ _
    rw [show p.1 + p.2 - (p'.1 + p'.2) = (p.1 - p'.1) + (p.2 - p'.2) by ring]
    exact (abs_add_le _ _).trans (by linarith)
  have h2 := Real.rpow_le_rpow (abs_nonneg _) h1 (by positivity : (0 : ℝ) ≤ a / 12)
  have h3 : (2 * δ) ^ (a / 12 : ℝ) ≤ 2 * δ ^ (a / 12) := by
    rw [Real.mul_rpow (by norm_num) hδ0]
    have h2a : (2 : ℝ) ^ (a / 12) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show a / 12 ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    have := mul_le_mul_of_nonneg_right h2a (Real.rpow_nonneg hδ0 (a / 12))
    linarith
  refine (mul_le_mul_of_nonneg_left (h2.trans h3) hK0).trans (le_of_eq ?_)
  rw [hK]; ring

end RegUnif
end QuantumZipper
