import QuantumZipper.Proofs.Zipper.SWCoreV3
import QuantumZipper.Proofs.Zipper.SWCoreV4
import QuantumZipper.Proofs.GFF.FrostmanReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-V (6): variance modulus of pushed semicircles in the map and the centre, over a class

Task SWC-V (`handoff/SW-CORE.md` §5, item (iii)). For a boundary class `BdryClass a b ρ M m`
(`a < b`, `ρ, m > 0`) there are `r₀ > 0` and `C` such that for `ψ₁, ψ₂` in the class,
`t₁, t₂ ∈ [a,b]` with `|t₁ − t₂| ≤ r < r₀`, and `δ ≥ 0` bounding `‖ψ₁ − ψ₂‖` on `B(t₂, r)`,

  `|kernelCov2 neumannH (fc(t₁,r).map ψ₁, fc(t₂,r).map ψ₂) (…)| ≤ C ((δ + |t₁ − t₂|)/r)^{1/6}`
                                                                 (`swcv_class_modulus`).

This is the variance modulus (in sup-norm of the maps and in the centre, relative to the scale `r`)
used for chaining over the class (SW, arXiv:1605.06171, Lemma 3.5, the modulus before (3.23),
p. 16). Proof: rescale both pushed semicircles by the common affine map
`u ↦ ψ₁(t₁) + r ψ₁'(t₁) u` (`swcv_push_affine`, `RegUnif.kernelCov2_map_affine`) and apply the
two-map unit bound `swcv_kernelCov2_two`; the class rescaling `bdryClass_rescale` (at radii `r` and
`2r`) gives the co-Lipschitz, boundedness and displacement constants. Own assembly.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif TwoPoint

open Classical in
/-- The rescaled map with base point `s0` and scale `lam`, made measurable off the unit disc. -/
def swcvTm (ψ : ℂ → ℂ) (t r s0 lam : ℝ) : ℂ → ℂ :=
  (closedBall (0 : ℂ) 1).piecewise (fun u => (ψ ((t : ℂ) + r * u) - s0) / lam) id

theorem measurable_swcvTm {ψ : ℂ → ℂ} {t r : ℝ} (hr : 0 < r)
    (hψc : ContinuousOn ψ (closedBall (t : ℂ) r)) (s0 lam : ℝ) :
    Measurable (swcvTm ψ t r s0 lam) := by
  classical
  have haffB : ∀ u ∈ closedBall (0 : ℂ) 1, (t : ℂ) + r * u ∈ closedBall (t : ℂ) r :=
    fun u hu => by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
      have : ‖u‖ ≤ 1 := by simpa using hu
      nlinarith
  have h1 : ContinuousOn (fun u : ℂ => ψ ((t : ℂ) + r * u)) (closedBall (0 : ℂ) 1) :=
    hψc.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn haffB
  have h2 : ContinuousOn (fun u : ℂ => (ψ ((t : ℂ) + r * u) - s0) / lam)
      (closedBall (0 : ℂ) 1) := (h1.sub continuousOn_const).div_const _
  unfold swcvTm
  convert ContinuousOn.measurable_piecewise h2 continuous_id.continuousOn measurableSet_closedBall

/-- **The pushed semicircle as an affine image of a displaced unit semicircle.** -/
theorem swcv_push_affine {ψ : ℂ → ℂ} {t r : ℝ} (hr : 0 < r)
    (hψc : ContinuousOn ψ (closedBall (t : ℂ) r)) (s0 : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    (foldedCircle (t : ℂ) r).map ψ =
      ((foldedCircle 0 1).map (swcvTm ψ t r s0 lam)).map (swhAff s0 lam) := by
  classical
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  have haffB : ∀ u ∈ closedBall (0 : ℂ) 1, (t : ℂ) + r * u ∈ closedBall (t : ℂ) r :=
    fun u hu => by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
      have : ‖u‖ ≤ 1 := by simpa using hu
      nlinarith
  have haeB : ∀ᵐ u ∂μ₀, u ∈ closedBall (0 : ℂ) 1 := swcv_ae_norm_fc01.mono fun u hu => by
    rw [mem_closedBall, dist_zero_right, hu]
  set ψm : ℂ → ℂ := (closedBall (t : ℂ) r).piecewise ψ id with hψm
  have hψmm : Measurable ψm :=
    ContinuousOn.measurable_piecewise hψc continuous_id.continuousOn measurableSet_closedBall
  have hfc : foldedCircle (t : ℂ) r = μ₀.map (swhAff t r) := swcv_fc_eq_map t hr
  have hnullT : (μ₀.map (swhAff t r)) (closedBall (t : ℂ) r)ᶜ = 0 := by
    rw [Measure.map_apply (measurable_swhAff t r) measurableSet_closedBall.compl]
    exact measure_mono_null (fun u hu hu1 => hu (haffB u hu1)) (ae_iff.1 haeB)
  have e1 : (foldedCircle (t : ℂ) r).map ψ = (foldedCircle (t : ℂ) r).map ψm := by
    rw [hfc]
    have hsub : {x : ℂ | ¬ ψ x = ψm x} ⊆ (closedBall (t : ℂ) r)ᶜ := fun x hx hxc => by
      apply hx
      rw [hψm, piecewise_eq_of_mem _ _ _ hxc]
    exact Measure.map_congr (ae_iff.2 (measure_mono_null hsub hnullT))
  rw [e1, hfc, Measure.map_map hψmm (measurable_swhAff t r),
    Measure.map_map (measurable_swhAff s0 lam) (measurable_swcvTm hr hψc s0 lam)]
  refine Measure.map_congr ?_
  filter_upwards [haeB] with u hu
  simp only [Function.comp_apply]
  have hmem : swhAff t r u ∈ closedBall (t : ℂ) r := haffB u hu
  rw [hψm, piecewise_eq_of_mem _ _ _ hmem, swcvTm, piecewise_eq_of_mem _ _ _ hu]
  unfold swhAff
  have hl0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam.ne'
  field_simp
  ring

/-- **Ball facts for a class map** (from `bdryClass_rescale`): on `B(t,r)`, `ψ` is
`(D/2)`-co-Lipschitz and `2D`-Lipschitz (`D = ψ'(t) ∈ [m, C]`) and preserves `Im ≥ 0`. -/
theorem swcv_ball_facts (a b ρ M m : ℝ) (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ BdryClass a b ρ M m, ∀ t ∈ Icc a b,
      ∀ r ∈ Ioo 0 r₁,
        (m ≤ (deriv ψ t).re ∧ (deriv ψ t).re ≤ C) ∧
        (∀ x ∈ closedBall (t : ℂ) r, ∀ y ∈ closedBall (t : ℂ) r,
          (deriv ψ t).re / 2 * ‖x - y‖ ≤ ‖ψ x - ψ y‖ ∧
            ‖ψ x - ψ y‖ ≤ 2 * (deriv ψ t).re * ‖x - y‖) ∧
        (∀ x ∈ closedBall (t : ℂ) r, 0 ≤ x.im → 0 ≤ (ψ x).im) := by
  obtain ⟨r₁, hr₁, C₁, hC₁, hres⟩ := bdryClass_rescale a b ρ M m hab hρ hm
  refine ⟨r₁, hr₁, C₁, hC₁, fun ψ hψ t ht r hr => ?_⟩
  have h := hres ψ hψ t ht r hr
  dsimp only at h
  obtain ⟨⟨-, hmD, hDC⟩, -, hlip, him, -⟩ := h
  set D : ℝ := (deriv ψ t).re with hD
  have hDpos : 0 < D := lt_of_lt_of_le hm hmD
  have hrD : 0 < r * D := mul_pos hr.1 hDpos
  have hψt : (ψ t).im = 0 := hψ.2.2.1 t ht
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.1.ne'
  have hu_of : ∀ x ∈ closedBall (t : ℂ) r, ((x - t) / r) ∈ closedBall (0 : ℂ) 1 ∧
      (t : ℂ) + r * ((x - t) / r) = x := fun x hx => by
    refine ⟨?_, by field_simp; ring⟩
    rw [mem_closedBall, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr.1, div_le_one hr.1, ← dist_eq_norm]
    exact hx
  refine ⟨⟨hmD, hDC⟩, fun x hx y hy => ?_, fun x hx hxi => ?_⟩
  · have h1 := hlip _ (hu_of x hx).1 _ (hu_of y hy).1
    rw [(hu_of x hx).2, (hu_of y hy).2] at h1
    have e3 : (ψ x - ψ t) / ((r : ℂ) * D) - (ψ y - ψ t) / ((r : ℂ) * D) =
        (ψ x - ψ y) / ((r : ℂ) * D) := by ring
    have e4 : (x - t) / (r : ℂ) - (y - t) / r = (x - y) / (r : ℂ) := by ring
    rw [e3, e4, norm_div, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr.1, abs_of_pos hDpos] at h1
    obtain ⟨h1a, h1b⟩ := h1
    rw [div_div, div_le_div_iff₀ (mul_pos hr.1 two_pos) hrD] at h1a
    rw [div_le_iff₀ hrD] at h1b
    constructor
    · nlinarith [norm_nonneg (x - y), norm_nonneg (ψ x - ψ y)]
    · calc ‖ψ x - ψ y‖ ≤ 2 * (‖x - y‖ / r) * (r * D) := h1b
        _ = 2 * D * ‖x - y‖ := by
          have hrne : r ≠ 0 := hr.1.ne'
          field_simp
  · have hui : 0 ≤ ((x - t) / r).im := by
      rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_nonneg hxi hr.1.le
    have h2 := him _ (hu_of x hx).1 hui
    rw [(hu_of x hx).2] at h2
    have e5 : ((ψ x - ψ t) / ((r : ℂ) * D)).im = (ψ x).im / (r * D) := by
      rw [← Complex.ofReal_mul, Complex.div_ofReal_im, Complex.sub_im, hψt, sub_zero]
    rw [e5] at h2
    by_contra hneg
    push_neg at hneg
    have := div_neg_of_neg_of_pos hneg hrD
    linarith

set_option maxHeartbeats 1000000 in
/-- **SWC-V (iii)**: variance modulus in the map and the centre, uniform over a class
(increments `δ, |t₁ − t₂| ≤ r`, the regime used for chaining). -/
theorem swcv_class_modulus (a b ρ M m : ℝ) (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ₁ ∈ BdryClass a b ρ M m,
      ∀ ψ₂ ∈ BdryClass a b ρ M m, ∀ t₁ ∈ Icc a b, ∀ t₂ ∈ Icc a b, ∀ r ∈ Ioo 0 r₀,
        |t₁ - t₂| ≤ r → ∀ δ : ℝ, 0 ≤ δ → δ ≤ r →
        (∀ z ∈ closedBall (t₂ : ℂ) r, ‖ψ₁ z - ψ₂ z‖ ≤ δ) →
        |kernelCov2 neumannH ((foldedCircle (t₁ : ℂ) r).map ψ₁,
            (foldedCircle (t₂ : ℂ) r).map ψ₂)
            ((foldedCircle (t₁ : ℂ) r).map ψ₁, (foldedCircle (t₂ : ℂ) r).map ψ₂)| ≤
          C * ((δ + |t₁ - t₂|) / r) ^ ((1 / 3 : ℝ) / 2) := by
  classical
  obtain ⟨r₁, hr₁, C₁, hC₁, hF⟩ := swcv_ball_facts a b ρ M m hab hρ hm
  set r₀ := min (r₁ / 2) (ρ / 4) with hr₀
  set c : ℝ := m / (2 * (C₁ + 1)) with hc
  have hc0 : 0 < c := by positivity
  set E : ℝ := 2 + 1 / m with hE
  have hE0 : 0 < E := by positivity
  set Bf : ℝ := 2 + 2 * E with hBf
  have hK0 : 0 ≤ holderK (12 / c + 1) Bf := holderK_nonneg (by positivity) (by positivity)
  refine ⟨r₀, lt_min (by linarith) (by linarith), 2 * (holderK (12 / c + 1) Bf *
      E ^ ((1 / 3 : ℝ) / 2)), by positivity,
    fun ψ₁ hψ₁ ψ₂ hψ₂ t₁ ht₁ t₂ ht₂ r hr htt δ hδ hδr hψδ => ?_⟩
  have hr2 : 2 * r < r₁ := by
    have := lt_of_lt_of_le hr.2 (min_le_left _ _); linarith
  have hrρ : r < ρ / 4 := lt_of_lt_of_le hr.2 (min_le_right _ _)
  obtain ⟨⟨hmD₁, hDC₁⟩, hL₁, -⟩ := hF ψ₁ hψ₁ t₁ ht₁ r ⟨hr.1, by linarith⟩
  obtain ⟨-, hL₁', -⟩ := hF ψ₁ hψ₁ t₁ ht₁ (2 * r) ⟨by linarith [hr.1], hr2⟩
  obtain ⟨⟨hmD₂, -⟩, hL₂, hI₂⟩ := hF ψ₂ hψ₂ t₂ ht₂ r ⟨hr.1, by linarith⟩
  obtain ⟨-, -, hI₁⟩ := hF ψ₁ hψ₁ t₁ ht₁ r ⟨hr.1, by linarith⟩
  set D₁ : ℝ := (deriv ψ₁ t₁).re with hD₁
  set D₂ : ℝ := (deriv ψ₂ t₂).re with hD₂
  have hD₁p : 0 < D₁ := lt_of_lt_of_le hm hmD₁
  have hD₂p : 0 < D₂ := lt_of_lt_of_le hm hmD₂
  set lam : ℝ := r * D₁ with hlam
  have hlam0 : 0 < lam := mul_pos hr.1 hD₁p
  set s0 : ℝ := (ψ₁ t₁).re with hs0
  have hψ₁t : ψ₁ t₁ = (s0 : ℂ) := Complex.ext (by simp [hs0]) (by simp [hψ₁.2.2.1 t₁ ht₁])
  have hψ₂t : (ψ₂ t₂).im = 0 := hψ₂.2.2.1 t₂ ht₂
  set B := closedBall (0 : ℂ) 1 with hB
  have haffB : ∀ (t : ℝ) (u : ℂ), u ∈ B → (t : ℂ) + r * u ∈ closedBall (t : ℂ) r :=
    fun t u hu => by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr.1]
      have : ‖u‖ ≤ 1 := by simpa [hB] using hu
      nlinarith
  have hcont : ∀ ψ ∈ BdryClass a b ρ M m, ∀ t ∈ Icc a b,
      ContinuousOn ψ (closedBall (t : ℂ) r) := fun ψ hψ t ht =>
    (hψ.1.mono fun z hz => by
      rw [mem_thickening_iff]
      refine ⟨(t : ℂ), ⟨t, ht, rfl⟩, ?_⟩
      have := mem_closedBall.1 hz
      linarith).continuousOn
  have hc₁ := hcont ψ₁ hψ₁ t₁ ht₁
  have hc₂ := hcont ψ₂ hψ₂ t₂ ht₂
  set A₁ := swcvTm ψ₁ t₁ r s0 lam with hA₁
  set A₂ := swcvTm ψ₂ t₂ r s0 lam with hA₂
  have hAe : ∀ (ψ : ℂ → ℂ) (t : ℝ), ∀ u ∈ B,
      swcvTm ψ t r s0 lam u = (ψ ((t : ℂ) + r * u) - s0) / lam := fun ψ t u hu => by
    unfold swcvTm; rw [piecewise_eq_of_mem _ _ _ hu]
  have hlamC : ‖(lam : ℂ)‖ = lam := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
  have hdiff : ∀ (ψ : ℂ → ℂ) (t : ℝ), ∀ u ∈ B, ∀ v ∈ B,
      ‖swcvTm ψ t r s0 lam u - swcvTm ψ t r s0 lam v‖ =
        ‖ψ ((t : ℂ) + r * u) - ψ ((t : ℂ) + r * v)‖ / lam := fun ψ t u hu v hv => by
    rw [hAe ψ t u hu, hAe ψ t v hv, ← sub_div, sub_sub_sub_cancel_right, norm_div, hlamC]
  have hxy : ∀ (t : ℝ) (u v : ℂ), ‖((t : ℂ) + r * u) - ((t : ℂ) + r * v)‖ = r * ‖u - v‖ :=
    fun t u v => by
      rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr.1]
  -- co-Lipschitz
  have hco₁ : ∀ u ∈ B, ∀ v ∈ B, c * ‖u - v‖ ≤ ‖A₁ u - A₁ v‖ := fun u hu v hv => by
    rw [hA₁, hdiff ψ₁ t₁ u hu v hv, le_div_iff₀ hlam0]
    have h1 := (hL₁ _ (haffB t₁ u hu) _ (haffB t₁ v hv)).1
    rw [hxy] at h1
    have hcle : c * D₁ ≤ D₁ / 2 := by
      rw [hc]; rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    have := norm_nonneg (u - v)
    rw [hlam]; nlinarith [mul_le_mul_of_nonneg_right hcle (mul_nonneg hr.1.le this)]
  have hco₂ : ∀ u ∈ B, ∀ v ∈ B, c * ‖u - v‖ ≤ ‖A₂ u - A₂ v‖ := fun u hu v hv => by
    rw [hA₂, hdiff ψ₂ t₂ u hu v hv, le_div_iff₀ hlam0]
    have h1 := (hL₂ _ (haffB t₂ u hu) _ (haffB t₂ v hv)).1
    rw [hxy] at h1
    have hcle : c * D₁ ≤ D₂ / 2 := by
      rw [hc, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    have := norm_nonneg (u - v)
    rw [hlam]; nlinarith [mul_le_mul_of_nonneg_right hcle (mul_nonneg hr.1.le this)]
  -- displacement
  have hdisp : ∀ u ∈ B, ‖A₁ u - A₂ u‖ ≤ E * ((δ + |t₁ - t₂|) / r) := fun u hu => by
    rw [hA₁, hA₂, hAe ψ₁ t₁ u hu, hAe ψ₂ t₂ u hu, ← sub_div, sub_sub_sub_cancel_right,
      norm_div, hlamC]
    have hx₂ : (t₂ : ℂ) + r * u ∈ closedBall (t₁ : ℂ) (2 * r) := by
      have h := haffB t₂ u hu
      rw [mem_closedBall, dist_eq_norm] at h ⊢
      have e : (t₂ : ℂ) + r * u - t₁ = ((t₂ : ℂ) + r * u - t₂) + ((t₂ - t₁ : ℝ) : ℂ) := by
        push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      linarith
    have hx₁ : (t₁ : ℂ) + r * u ∈ closedBall (t₁ : ℂ) (2 * r) :=
      closedBall_subset_closedBall (by linarith [hr.1]) (haffB t₁ u hu)
    have h1 := (hL₁' _ hx₁ _ hx₂).2
    have e1 : ‖((t₁ : ℂ) + r * u) - ((t₂ : ℂ) + r * u)‖ = |t₁ - t₂| := by
      rw [add_sub_add_right_eq_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [e1] at h1
    have h2 := hψδ _ (haffB t₂ u hu)
    have htri : ‖ψ₁ ((t₁ : ℂ) + r * u) - ψ₂ ((t₂ : ℂ) + r * u)‖ ≤ 2 * D₁ * |t₁ - t₂| + δ := by
      calc _ = ‖(ψ₁ ((t₁ : ℂ) + r * u) - ψ₁ ((t₂ : ℂ) + r * u)) +
            (ψ₁ ((t₂ : ℂ) + r * u) - ψ₂ ((t₂ : ℂ) + r * u))‖ := by ring_nf
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
    rw [div_le_iff₀ hlam0]
    refine htri.trans ?_
    have hm1 : 1 ≤ D₁ / m := (one_le_div hm).2 hmD₁
    have hx0 := abs_nonneg (t₁ - t₂)
    rw [hE, hlam]
    have e2 : (2 + 1 / m) * ((δ + |t₁ - t₂|) / r) * (r * D₁) =
        2 * D₁ * δ + 2 * D₁ * |t₁ - t₂| + (D₁ / m) * δ + (D₁ / m) * |t₁ - t₂| := by
      have hrne : r ≠ 0 := hr.1.ne'
      have hmne : m ≠ 0 := hm.ne'
      field_simp; ring
    rw [e2]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ D₁ / m) hx0, mul_nonneg hD₁p.le hδ]
  have hΔ : E * ((δ + |t₁ - t₂|) / r) ≤ 2 * E := by
    have : (δ + |t₁ - t₂|) / r ≤ 2 := by
      rw [div_le_iff₀ hr.1]; linarith
    nlinarith
  -- bounds
  have hA₁0 : A₁ 0 = 0 := by
    rw [hA₁, hAe ψ₁ t₁ 0 (by simp [hB]), mul_zero, add_zero, hψ₁t, sub_self, zero_div]
  have hb₁ : ∀ u ∈ B, ‖A₁ u‖ ≤ Bf := fun u hu => by
    have h0B : (0 : ℂ) ∈ B := by simp [hB]
    have h := hdiff ψ₁ t₁ u hu 0 h0B
    rw [← hA₁, hA₁0, sub_zero] at h
    rw [h, div_le_iff₀ hlam0]
    have h1 := (hL₁ _ (haffB t₁ u hu) _ (haffB t₁ 0 h0B)).2
    rw [hxy, sub_zero] at h1
    have hu1 : ‖u‖ ≤ 1 := by simpa [hB] using hu
    have h2 : 2 * D₁ * (r * ‖u‖) ≤ 2 * (r * D₁) := by
      have := mul_le_mul_of_nonneg_left hu1 (mul_nonneg (mul_nonneg zero_le_two hD₁p.le) hr.1.le)
      nlinarith
    have h3 : 2 * (r * D₁) ≤ Bf * lam := by
      rw [hBf, hlam]; nlinarith [mul_pos hr.1 hD₁p]
    linarith
  have hb₂ : ∀ u ∈ B, ‖A₂ u‖ ≤ Bf := fun u hu => by
    have hb₁' : ‖A₁ u‖ ≤ 2 := by
      have h0B : (0 : ℂ) ∈ B := by simp [hB]
      have h := hdiff ψ₁ t₁ u hu 0 h0B
      rw [← hA₁, hA₁0, sub_zero] at h
      rw [h, div_le_iff₀ hlam0]
      have h1 := (hL₁ _ (haffB t₁ u hu) _ (haffB t₁ 0 h0B)).2
      rw [hxy, sub_zero] at h1
      have hu1 : ‖u‖ ≤ 1 := by simpa [hB] using hu
      have h2 : 2 * D₁ * (r * ‖u‖) ≤ 2 * (r * D₁) := by
        have := mul_le_mul_of_nonneg_left hu1
          (mul_nonneg (mul_nonneg zero_le_two hD₁p.le) hr.1.le)
        nlinarith
      rw [hlam]; linarith
    calc ‖A₂ u‖ = ‖A₁ u - (A₁ u - A₂ u)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A₁ u‖ + ‖A₁ u - A₂ u‖ := norm_sub_le _ _
      _ ≤ 2 + 2 * E := add_le_add hb₁' ((hdisp u hu).trans hΔ)
      _ = Bf := by rw [hBf]
  -- admissibility of the unit pair
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  have haeB : ∀ᵐ u ∂μ₀, u ∈ B := swcv_ae_norm_fc01.mono fun u hu => by
    rw [hB, mem_closedBall, dist_zero_right, hu]
  have haeH : ∀ᵐ u ∂μ₀, u ∈ Hbar := by
    have hHm : MeasurableSet {x : ℂ | x ∈ Hbar} :=
      measurableSet_le measurable_const Complex.measurable_im
    rw [hμ₀, foldedCircle, ae_map_iff measurable_foldH.aemeasurable hHm]
    exact Eventually.of_forall fun w => CircleFubini.foldH_mem_Hbar' w
  have hK : IsCompact (B ∩ Hbar) := (isCompact_closedBall 0 1).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hKc : μ₀ (B ∩ Hbar)ᶜ = 0 := by
    have h := ae_iff.1 (haeB.and haeH)
    simpa [compl_def] using h
  have hadm0 : IsAdmissibleH μ₀ := D3Plus.isAdmissibleH_foldedCircle' 0 one_pos
  have hadm : ∀ (ψ : ℂ → ℂ) (t : ℝ), ContinuousOn ψ (closedBall (t : ℂ) r) →
      (∀ x ∈ closedBall (t : ℂ) r, 0 ≤ x.im → 0 ≤ (ψ x).im) →
      (∀ u ∈ B, ∀ v ∈ B, c * ‖u - v‖ ≤
        ‖swcvTm ψ t r s0 lam u - swcvTm ψ t r s0 lam v‖) →
      IsAdmissibleH (μ₀.map (swcvTm ψ t r s0 lam)) := fun ψ t hψc hIm hco => by
    have hf : ContinuousOn (fun u : ℂ => (ψ ((t : ℂ) + r * u) - s0) / lam) B :=
      ((hψc.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
        (haffB t)).sub continuousOn_const).div_const _
    refine isAdmissibleH_map hadm0 hK hKc (measurable_swcvTm hr.1 hψc s0 lam)
      ((hf.congr fun u hu => hAe ψ t u hu).mono inter_subset_left) ?_ hc0
      fun x hx y hy => hco x hx.1 y hy.1
    rintro _ ⟨u, ⟨hu, huH⟩, rfl⟩
    show 0 ≤ (swcvTm ψ t r s0 lam u).im
    rw [hAe ψ t u hu, Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
    refine div_nonneg (hIm _ (haffB t u hu) ?_) hlam0.le
    have : (0 : ℝ) ≤ u.im := huH
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
      zero_mul, add_zero]
    exact mul_nonneg hr.1.le this
  have hadm1 := hadm ψ₁ t₁ hc₁ hI₁ hco₁
  have hadm2 := hadm ψ₂ t₂ hc₂ hI₂ hco₂
  have hmass : (μ₀.map A₁) univ = (μ₀.map A₂) univ := by
    rw [Measure.map_apply (measurable_swcvTm hr.1 hc₁ s0 lam) MeasurableSet.univ,
      Measure.map_apply (measurable_swcvTm hr.1 hc₂ s0 lam) MeasurableSet.univ,
      preimage_univ, preimage_univ]
  rw [swcv_push_affine hr.1 hc₁ s0 hlam0, swcv_push_affine hr.1 hc₂ s0 hlam0]
  have hinv := kernelCov2_map_affine s0 hlam0 ⟨(μ₀.map A₁, μ₀.map A₂), hadm1, hadm2, hmass⟩
  simp only at hinv
  rw [hinv]
  have hx0 : 0 ≤ (δ + |t₁ - t₂|) / r := div_nonneg (by positivity) hr.1.le
  have htwo := swcv_kernelCov2_two (measurable_swcvTm hr.1 hc₁ s0 lam)
    (measurable_swcvTm hr.1 hc₂ s0 lam) (mul_nonneg hE0.le hx0) (by positivity) hc0
    hdisp hb₁ hb₂ hco₁ hco₂
  refine htwo.trans (le_of_eq ?_)
  rw [Real.mul_rpow hE0.le hx0]
  ring

end SWCore
end QuantumZipper
