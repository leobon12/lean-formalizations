import LQGDimension.LFPP.CouplingAux3
import LQGDimension.Blueprint.Existence

/-!
# Existence track: the circle-average covariance kernel with different radii

We prove the three kernel nodes of `Blueprint.Existence`:

* `gffCovPSD` (`GffCovPSD`): `gffCircleCov` is positive semidefinite on finite sets of
  (radius, centre) pairs with positive radii.
* `gffCovContinuous` (`GffCovContinuous`): `gffCircleCov` is jointly continuous for positive
  radii.
* `gffIncrementBound` (`GffIncrementBound`): `Var(h_ε(z) − h_δ(w)) ≤ 5 (m+1) ‖(ε,z) − (δ,w)‖`
  on `box m`.

## Strategy

* `gffCircleCov_eq_lPair2` generalises `Coupling.gffCircleCov_eq_lPair` to two radii:
  `gffCircleCov ε z δ w = -L(σ_{z,ε}, σ_{w,δ}) + L(σ_{z,ε}, σ_{0,1}) + L(σ_{0,1}, σ_{w,δ})
  - L(σ_{0,1}, σ_{0,1})` with `L = lPair` the logarithmic pairing.
* **PSD.** `Coupling.circ_heatRep` already handles two arbitrary radii, so the heat-kernel
  representation `gffCircleCov p q = ∫_0^∞ Q_t(p, q) dt/t` holds with
  `Q_t(p, q) = ∫ (C_p C_q + S_p S_q) dγ`, where `C_p, S_p` are the cosine/sine Fourier features
  of the zero-mass measure `σ_p − σ_{0,1}`.  Each `Q_t` is a Gram kernel, hence PSD.
* **Continuity.** By Jensen's formula the inner circle average is explicit, so
  `gffCircleCov ε z δ w` is a sum of three parametric interval integrals of integrands that are
  continuous for `δ > 0`.
* **Increments.** The `σ_{0,1}` terms cancel:
  `C(s,s) + C(t,t) − 2C(s,t) = −log ε − log δ + 2 L(σ_{z,ε}, σ_{w,δ})`, and
  `L(σ_{z,ε}, σ_{w,δ}) ≤ log δ + log⁺ ((‖w − z‖ + ε)/δ)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.GffKernel

open Coupling HeatKernel

/-! ## 1. The covariance through logarithmic pairings, two radii -/

/-- `gffCircleCov` with two (possibly different) radii, in terms of `lPair`. -/
theorem gffCircleCov_eq_lPair2 (z w : ℂ) (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    gffCircleCov ε z δ w = -lPair (circMeas z ε) (circMeas w δ) +
      lPair (circMeas z ε) (circMeas 0 1) + lPair (circMeas 0 1) (circMeas w δ) -
        lPair (circMeas 0 1) (circMeas 0 1) := by
  rw [gffCircleCov_eq_integral, lPair_unit_right, lPair_unit_left w hδ, lPair_unit_unit,
    sub_zero]
  have hL := integrable_log_circ_prod z w ε hδ
  have hPx := integrable_posLog_norm_circ z ε
  have hPy := integrable_posLog_norm_circ w δ
  have hG : ∀ x y : ℂ, gffGreen x y = -Real.log ‖x - y‖ + log⁺ ‖x‖ + log⁺ ‖y‖ := by
    intro x y
    rw [gffGreen, posLog_eq_log_max_one (norm_nonneg x), posLog_eq_log_max_one (norm_nonneg y),
      max_comm 1 ‖x‖, max_comm 1 ‖y‖]
  have hin : ∀ x : ℂ, ∫ y, gffGreen x y ∂circMeas w δ =
      -∫ y, Real.log ‖x - y‖ ∂circMeas w δ + log⁺ ‖x‖ + ∫ y, log⁺ ‖y‖ ∂circMeas w δ := by
    intro x
    simp_rw [hG x]
    have h1 : Integrable (fun y => -Real.log ‖x - y‖) (circMeas w δ) :=
      (integrable_log_norm_sub_circ x w δ).neg
    have h2 : Integrable (fun y => -Real.log ‖x - y‖ + log⁺ ‖x‖) (circMeas w δ) :=
      h1.add (integrable_const _)
    rw [integral_add h2 hPy, integral_add h1 (integrable_const _), integral_neg]
    simp
  simp_rw [hin]
  have hI : Integrable (fun x => ∫ y, Real.log ‖x - y‖ ∂circMeas w δ) (circMeas z ε) :=
    hL.integral_prod_left
  have k1 : Integrable (fun x => -∫ y, Real.log ‖x - y‖ ∂circMeas w δ) (circMeas z ε) :=
    hI.neg
  have k2 : Integrable (fun x => -∫ y, Real.log ‖x - y‖ ∂circMeas w δ + log⁺ ‖x‖)
      (circMeas z ε) := k1.add hPx
  rw [integral_add k2 (integrable_const _), integral_add k1 hPx, integral_neg,
    lPair, integral_prod _ hL]
  simp

/-! ## 2. The heat-kernel (Gram) representation and positive semidefiniteness -/

/-- Cosine feature of the zero-mass measure `σ_{p.2, p.1} − σ_{0,1}` at scale `t`. -/
def cJ (t : ℝ) (p : ℝ × ℂ) (ξ : ℂ) : ℝ := cL t 1 (-1) (circMeas p.2 p.1) (circMeas 0 1) ξ

/-- Sine feature of the zero-mass measure `σ_{p.2, p.1} − σ_{0,1}` at scale `t`. -/
def sJ (t : ℝ) (p : ℝ × ℂ) (ξ : ℂ) : ℝ := sL t 1 (-1) (circMeas p.2 p.1) (circMeas 0 1) ξ

/-- The scale-`t` Gram kernel `Q_t(p, q)`. -/
def Qt (t : ℝ) (p q : ℝ × ℂ) : ℝ :=
  ∫ ξ, (cJ t p ξ * cJ t q ξ + sJ t p ξ * sJ t q ξ) ∂(stdGaussian ℂ)

/-- The kernel `∫_0^∞ Q_t(p, q) dt/t`. -/
def Kg (p q : ℝ × ℂ) : ℝ := ∫ t in Ioi 0, Qt t p q / t

lemma integrable_QtIntegrand (t : ℝ) (p q : ℝ × ℂ) :
    Integrable (fun ξ => cJ t p ξ * cJ t q ξ + sJ t p ξ * sJ t q ξ) (stdGaussian ℂ) :=
  integrable_lin t _ _ _ _ _ _ _ _

lemma Qt_eq (t : ℝ) (p q : ℝ × ℂ) : Qt t p q =
    gPair t (circMeas p.2 p.1) (circMeas q.2 q.1) - gPair t (circMeas p.2 p.1) (circMeas 0 1) -
      gPair t (circMeas 0 1) (circMeas q.2 q.1) + gPair t (circMeas 0 1) (circMeas 0 1) := by
  rw [Qt]
  simp only [cJ, sJ]
  rw [integral_lin]
  ring

lemma Qt_comm (t : ℝ) (p q : ℝ × ℂ) : Qt t p q = Qt t q p := by
  unfold Qt; congr 1; funext ξ; ring

lemma Kg_comm (p q : ℝ × ℂ) : Kg p q = Kg q p := by
  unfold Kg; simp_rw [Qt_comm _ p q]

lemma Qt_div (t : ℝ) (p q : ℝ × ℂ) : Qt t p q / t =
    Hc t (circMeas p.2 p.1) (circMeas q.2 q.1) - Hc t (circMeas p.2 p.1) (circMeas 0 1) -
      Hc t (circMeas 0 1) (circMeas q.2 q.1) + Hc t (circMeas 0 1) (circMeas 0 1) := by
  rw [Qt_eq]; simp only [Hc]; ring

lemma integrableOn_Qt (p : ℝ × ℂ) {q : ℝ × ℂ} (hq : 0 < q.1) :
    IntegrableOn (fun t => Qt t p q / t) (Ioi 0) := by
  have h1 := (circ_heatRep' p.2 q.2 p.1 hq).1
  have h2 := (circ_heatRep' p.2 0 p.1 one_pos).1
  have h3 := (circ_heatRep' 0 q.2 1 hq).1
  have h4 := (circ_heatRep' 0 0 1 one_pos).1
  refine (((h1.sub h2).sub h3).add h4).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Pi.sub_apply, Qt_div]

/-- The heat-kernel representation of `gffCircleCov` with two radii. -/
theorem Kg_eq (p : ℝ × ℂ) {q : ℝ × ℂ} (hq : 0 < q.1) :
    Kg p q = gffCircleCov p.1 p.2 q.1 q.2 := by
  unfold Kg
  simp_rw [Qt_div]
  obtain ⟨h1, e1⟩ := circ_heatRep' p.2 q.2 p.1 hq
  obtain ⟨h2, e2⟩ := circ_heatRep' p.2 0 p.1 one_pos
  obtain ⟨h3, e3⟩ := circ_heatRep' 0 q.2 1 hq
  obtain ⟨h4, e4⟩ := circ_heatRep' 0 0 1 one_pos
  have k1 : IntegrableOn (fun t => Hc t (circMeas p.2 p.1) (circMeas q.2 q.1) -
      Hc t (circMeas p.2 p.1) (circMeas 0 1)) (Ioi 0) := h1.sub h2
  have k2 : IntegrableOn (fun t => Hc t (circMeas p.2 p.1) (circMeas q.2 q.1) -
      Hc t (circMeas p.2 p.1) (circMeas 0 1) - Hc t (circMeas 0 1) (circMeas q.2 q.1))
      (Ioi 0) := k1.sub h3
  rw [integral_add k2 h4, integral_sub k1 h3, integral_sub h1 h2, e1, e2, e3, e4,
    gffCircleCov_eq_lPair2 p.2 q.2 p.1 hq]
  ring

lemma quad_Qt_nonneg {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ℝ) (k : ι → ℝ × ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, x i * x j * Qt t (k i) (k j) := by
  set Φ : ι → ι → ℂ → ℝ := fun i j ξ => x i * x j *
    (cJ t (k i) ξ * cJ t (k j) ξ + sJ t (k i) ξ * sJ t (k j) ξ) with hΦ
  have hint : ∀ i j, Integrable (Φ i j) (stdGaussian ℂ) := fun i j =>
    (integrable_QtIntegrand t (k i) (k j)).const_mul _
  have heq : ∑ i ∈ s, ∑ j ∈ s, x i * x j * Qt t (k i) (k j) =
      ∫ ξ, ∑ i ∈ s, ∑ j ∈ s, Φ i j ξ ∂(stdGaussian ℂ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ]
    simp only
    rw [integral_const_mul, Qt]
  rw [heq]
  refine integral_nonneg fun ξ => ?_
  have : ∑ i ∈ s, ∑ j ∈ s, Φ i j ξ = (∑ i ∈ s, x i * cJ t (k i) ξ) ^ 2 +
      (∑ i ∈ s, x i * sJ t (k i) ξ) ^ 2 := by
    simp only [hΦ, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  positivity

open Matrix in
/-- `Kg` is positive semidefinite on every finite set of positive-radius indices. -/
theorem Kg_psd (F : Finset (ℝ × ℂ)) (hF : ∀ p ∈ F, 0 < p.1) : PSDOn F Kg := by
  unfold PSDOn
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, Kg_comm (j : ℝ × ℂ) i]
  · intro x
    simp only [star_trivial]
    have hint : ∀ i j : F, IntegrableOn (fun t => Qt t i j / t) (Ioi 0) :=
      fun i j => integrableOn_Qt i (hF j j.2)
    have heq : x ⬝ᵥ ((Matrix.of fun i j : F => Kg i j) *ᵥ x) =
        ∫ t in Ioi 0, ∑ i : F, ∑ j : F, x i * x j * (Qt t i j / t) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (hint i j).const_mul _)]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, Kg]
      ring
    rw [heq]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have h := quad_Qt_nonneg Finset.univ x t (fun i : F => (i : ℝ × ℂ))
    have : ∑ i : F, ∑ j : F, x i * x j * (Qt t i j / t) =
        (∑ i : F, ∑ j : F, x i * x j * Qt t i j) / t := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact div_nonneg h (le_of_lt ht)

/-! ## 3. Explicit form and continuity -/

/-- `gffCircleCov` as three explicit interval integrals (Jensen's formula for the inner
average). -/
lemma gffCircleCov_closed (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) (z w : ℂ) :
    gffCircleCov ε z δ w =
      -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
          (Real.log δ + log⁺ (δ⁻¹ * ‖w - circleMap z ε θ‖))) +
        (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, log⁺ ‖circleMap z ε θ‖) +
        (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, log⁺ ‖circleMap w δ θ‖ := by
  have m1 : AEStronglyMeasurable (fun x : ℂ => Real.log δ + log⁺ (δ⁻¹ * ‖w - x‖))
      (circMeas z ε) := (by fun_prop : Continuous fun x : ℂ =>
        Real.log δ + log⁺ (δ⁻¹ * ‖w - x‖)).aestronglyMeasurable
  have m2 : ∀ (c : ℂ) (r : ℝ), AEStronglyMeasurable (fun x : ℂ => log⁺ ‖x‖) (circMeas c r) :=
    fun c r => (by fun_prop : Continuous fun x : ℂ => log⁺ ‖x‖).aestronglyMeasurable
  rw [gffCircleCov_eq_lPair2 z w ε hδ, lPair_circ z w ε hδ, lPair_unit_right,
    lPair_unit_left w hδ, lPair_unit_unit, sub_zero, integral_circMeas' m1,
    integral_circMeas' (m2 z ε), integral_circMeas' (m2 w δ)]

/-- The positive-radius domain. -/
def posDom : Set ((ℝ × ℂ) × (ℝ × ℂ)) := {x | 0 < x.1.1 ∧ 0 < x.2.1}

theorem continuousOn_gffCircleCov :
    ContinuousOn (fun x : (ℝ × ℂ) × (ℝ × ℂ) => gffCircleCov x.1.1 x.1.2 x.2.1 x.2.2) posDom := by
  rw [continuousOn_iff_continuous_domRestrict]
  -- the three integrands, continuous on `posDom × ℝ`
  set f1 : posDom → ℝ → ℝ := fun x θ =>
    Real.log (x : (ℝ × ℂ) × (ℝ × ℂ)).2.1 + log⁺ ((x : (ℝ × ℂ) × (ℝ × ℂ)).2.1⁻¹ *
      ‖(x : (ℝ × ℂ) × (ℝ × ℂ)).2.2 -
        circleMap (x : (ℝ × ℂ) × (ℝ × ℂ)).1.2 (x : (ℝ × ℂ) × (ℝ × ℂ)).1.1 θ‖) with hf1
  set f2 : posDom → ℝ → ℝ := fun x θ =>
    log⁺ ‖circleMap (x : (ℝ × ℂ) × (ℝ × ℂ)).1.2 (x : (ℝ × ℂ) × (ℝ × ℂ)).1.1 θ‖ with hf2
  set f3 : posDom → ℝ → ℝ := fun x θ =>
    log⁺ ‖circleMap (x : (ℝ × ℂ) × (ℝ × ℂ)).2.2 (x : (ℝ × ℂ) × (ℝ × ℂ)).2.1 θ‖ with hf3
  have hδ : Continuous fun p : posDom × ℝ => (p.1 : (ℝ × ℂ) × (ℝ × ℂ)).2.1 := by fun_prop
  have hδ0 : ∀ p : posDom × ℝ, (p.1 : (ℝ × ℂ) × (ℝ × ℂ)).2.1 ≠ 0 := fun p => p.1.2.2.ne'
  have c1 : Continuous (Function.uncurry f1) := by
    have hcm : Continuous fun p : posDom × ℝ => (p.1 : (ℝ × ℂ) × (ℝ × ℂ)).2.2 -
        circleMap (p.1 : (ℝ × ℂ) × (ℝ × ℂ)).1.2 (p.1 : (ℝ × ℂ) × (ℝ × ℂ)).1.1 p.2 := by
      unfold circleMap; fun_prop
    exact (hδ.log hδ0).add (continuous_posLog.comp ((hδ.inv₀ hδ0).mul hcm.norm))
  have c2 : Continuous (Function.uncurry f2) := by
    simp only [hf2]; unfold circleMap; fun_prop
  have c3 : Continuous (Function.uncurry f3) := by
    simp only [hf3]; unfold circleMap; fun_prop
  have i1 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) c1 0 (2 * π)
  have i2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) c2 0 (2 * π)
  have i3 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) c3 0 (2 * π)
  have heq : posDom.domRestrict (fun x : (ℝ × ℂ) × (ℝ × ℂ) =>
      gffCircleCov x.1.1 x.1.2 x.2.1 x.2.2) = fun x =>
        -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f1 x θ) + (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, f2 x θ)
          + (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f3 x θ := by
    funext x
    simp only [Set.domRestrict_apply, hf1, hf2, hf3]
    exact gffCircleCov_closed _ x.2.2 _ _
  rw [heq]
  exact ((continuous_const.mul i1).neg.add (continuous_const.mul i2)).add
    (continuous_const.mul i3)

/-! ## 4. Increments -/

/-- The variance of an increment: the `σ_{0,1}` terms cancel. -/
lemma var_eq {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z w : ℂ) :
    gffCircleCov ε z ε z + gffCircleCov δ w δ w - 2 * gffCircleCov ε z δ w =
      -Real.log ε - Real.log δ + 2 * lPair (circMeas z ε) (circMeas w δ) := by
  rw [gffCircleCov_eq_lPair2 z z ε hε, gffCircleCov_eq_lPair2 w w δ hδ,
    gffCircleCov_eq_lPair2 z w ε hδ, lPair_unit_unit, lPair_self z hε, lPair_self w hδ,
    lPair_unit_right z ε, lPair_unit_right w δ, lPair_unit_left z hε, lPair_unit_left w hδ]
  ring

lemma lPair_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z w : ℂ) :
    lPair (circMeas z ε) (circMeas w δ) ≤ Real.log δ + log⁺ (δ⁻¹ * (‖w - z‖ + ε)) := by
  rw [lPair_circ z w ε hδ]
  have hI : Integrable (fun x => Real.log δ + log⁺ (δ⁻¹ * ‖w - x‖)) (circMeas z ε) := by
    refine (integrable_log_circ_prod z w ε hδ).integral_prod_left.congr
      (ae_of_all _ fun x => ?_)
    exact integral_log_norm_sub_circ x w hδ
  calc ∫ x, (Real.log δ + log⁺ (δ⁻¹ * ‖w - x‖)) ∂circMeas z ε
      ≤ ∫ _x, (Real.log δ + log⁺ (δ⁻¹ * (‖w - z‖ + ε))) ∂circMeas z ε := by
        refine integral_mono_ae hI (integrable_const _) ?_
        filter_upwards [ae_circMeas z ε] with x hx
        rw [abs_of_pos hε] at hx
        have h1 : ‖w - x‖ ≤ ‖w - z‖ + ε := by
          calc ‖w - x‖ = ‖(w - z) + (z - x)‖ := by congr 1; ring
            _ ≤ ‖w - z‖ + ‖z - x‖ := norm_add_le _ _
            _ = ‖w - z‖ + ε := by rw [norm_sub_rev z x, hx]
        have hnn : 0 ≤ δ⁻¹ * ‖w - x‖ := mul_nonneg (inv_nonneg.2 hδ.le) (norm_nonneg _)
        have h2 : log⁺ (δ⁻¹ * ‖w - x‖) ≤ log⁺ (δ⁻¹ * (‖w - z‖ + ε)) :=
          posLog_le_posLog (by linarith) (mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hδ.le))
        linarith
    _ = Real.log δ + log⁺ (δ⁻¹ * (‖w - z‖ + ε)) := by simp

/-- The increment bound with explicit constants, for radii `≥ 1/(m+1)`. -/
lemma var_le {ε δ M : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hεM : ε⁻¹ ≤ M) (hδM : δ⁻¹ ≤ M)
    (z w : ℂ) :
    gffCircleCov ε z ε z + gffCircleCov δ w δ w - 2 * gffCircleCov ε z δ w ≤
      |ε - δ| * M + 2 * ((‖w - z‖ + |ε - δ|) * M) := by
  have hM : 0 ≤ M := (inv_nonneg.2 hε.le).trans hεM
  rw [var_eq hε hδ z w]
  have hl := lPair_le hε hδ z w
  have e1 : Real.log δ - Real.log ε ≤ |ε - δ| * M := by
    rw [← Real.log_div hδ.ne' hε.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hδ hε)
    have hεinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    calc Real.log (δ / ε) ≤ δ / ε - 1 := h
      _ = (δ - ε) * ε⁻¹ := by rw [div_eq_mul_inv]; linear_combination hεinv
      _ ≤ |ε - δ| * ε⁻¹ := mul_le_mul_of_nonneg_right
          (by rw [abs_sub_comm]; exact le_abs_self _) (inv_nonneg.2 hε.le)
      _ ≤ |ε - δ| * M := mul_le_mul_of_nonneg_left hεM (abs_nonneg _)
  have e2 : log⁺ (δ⁻¹ * (‖w - z‖ + ε)) ≤ (‖w - z‖ + |ε - δ|) * M := by
    rw [posLog_apply]
    refine max_le (by positivity) ?_
    have hy : 0 < δ⁻¹ * (‖w - z‖ + ε) := by positivity
    have hδinv : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ.ne'
    calc Real.log (δ⁻¹ * (‖w - z‖ + ε)) ≤ δ⁻¹ * (‖w - z‖ + ε) - 1 :=
          Real.log_le_sub_one_of_pos hy
      _ = (‖w - z‖ + (ε - δ)) * δ⁻¹ := by linear_combination hδinv
      _ ≤ (‖w - z‖ + |ε - δ|) * δ⁻¹ := mul_le_mul_of_nonneg_right
          (by linarith [le_abs_self (ε - δ)]) (inv_nonneg.2 hδ.le)
      _ ≤ (‖w - z‖ + |ε - δ|) * M := mul_le_mul_of_nonneg_left hδM (by positivity)
  linarith

end LQGDimension.GffKernel

namespace LQGDimension

open GffKernel

/-- **Node `GffCovPSD`.** -/
theorem gffCovPSD : Blueprint.Existence.GffCovPSD := by
  intro F hF
  have h := Kg_psd F hF
  unfold PSDOn at h ⊢
  convert h using 1
  ext i j
  simp only [Matrix.of_apply]
  exact (Kg_eq _ (hF j j.2)).symm

/-- **Node `GffCovContinuous`.** -/
theorem gffCovContinuous : Blueprint.Existence.GffCovContinuous :=
  continuousOn_gffCircleCov

/-- **Node `GffIncrementBound`**, with `L_m = 5 (m + 1)`. -/
theorem gffIncrementBound : Blueprint.Existence.GffIncrementBound := by
  intro m
  refine ⟨5 * ((m : ℝ) + 1), fun s hs t ht => ?_⟩
  obtain ⟨ε, z⟩ := s
  obtain ⟨δ, w⟩ := t
  simp only [Blueprint.Existence.box, Set.mem_prod, Set.mem_Icc] at hs ht
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hε : 0 < ε := lt_of_lt_of_le (by positivity) hs.1.1
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) ht.1.1
  have hεM : ε⁻¹ ≤ (m : ℝ) + 1 := by
    rw [inv_le_comm₀ hε hm, ← one_div]; exact hs.1.1
  have hδM : δ⁻¹ ≤ (m : ℝ) + 1 := by
    rw [inv_le_comm₀ hδ hm, ← one_div]; exact ht.1.1
  have hN1 : |ε - δ| ≤ ‖((ε, z) - (δ, w) : ℝ × ℂ)‖ := by
    rw [Prod.mk_sub_mk, ← Real.norm_eq_abs]; exact norm_fst_le (ε - δ, z - w)
  have hN2 : ‖w - z‖ ≤ ‖((ε, z) - (δ, w) : ℝ × ℂ)‖ := by
    rw [Prod.mk_sub_mk, norm_sub_rev]; exact norm_snd_le (ε - δ, z - w)
  have h := var_le hε hδ hεM hδM z w
  have f1 : |ε - δ| * ((m : ℝ) + 1) ≤ ‖((ε, z) - (δ, w) : ℝ × ℂ)‖ * ((m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hN1 hm.le
  have f2 : ‖w - z‖ * ((m : ℝ) + 1) ≤ ‖((ε, z) - (δ, w) : ℝ × ℂ)‖ * ((m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hN2 hm.le
  show gffCircleCov ε z ε z + gffCircleCov δ w δ w - 2 * gffCircleCov ε z δ w ≤
    5 * ((m : ℝ) + 1) * ‖((ε, z) - (δ, w) : ℝ × ℂ)‖
  nlinarith

end LQGDimension
