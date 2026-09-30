import QuantumZipper.Proofs.Thm18.G1SideExact
import QuantumZipper.Proofs.Zipper.SWCoreB7Fam
import QuantumZipper.Proofs.Zipper.SWCoreB7bWTLem

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (7): uniformity over the dilated test functions `f(c ·)`, `c ∈ [1,2]`

The offset radii `c 2^{-k}` of the side boundary limit become, by
`G1Side.integral_bdryR_offset_of_avg`, the dyadic radius for the dilated test function `f(c ·)`.
Here the uniform transport of `G1Side.ae_wedge_transport_family` (one test function at a time) is
upgraded to the totally bounded family `{f(c ·) : c ∈ [1,2]}` (`ae_wedge_offset_uniform`), with
`SWCore.unif_testFamily`; the integrability of the bump comes from the continuity of the dyadic
averages in the centre (`G1Side.ae_wedge_family_exact`), and the Lipschitz bound of the limit
functional from `SWCore.abs_sub_le_of_limits`. Sheffield–Wang arXiv:1605.06171 Thm 1.4
(continuous radii) through the dilation; own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

/-- A continuous function vanishing off `[a,b]` is integrable for `bdryApprox` when the dyadic
averages are continuous on `[a,b]`. -/
theorem integrable_bdryApprox_of_continuousOn (γ : ℝ) {Z : FieldSample} {k : ℕ} {a b : ℝ}
    (hc : ContinuousOn (fun u : ℝ => avgReg Z k (u : ℂ)) (Icc a b)) {h : ℝ → ℝ}
    (hh : Continuous h) (hs : ∀ u, u ∉ Icc a b → h u = 0) :
    Integrable h (bdryApprox γ Z k) := by
  have hdc : ContinuousOn (fun u : ℝ => radius k ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg Z k (u : ℂ))) (Icc a b) :=
    continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hc))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  have hfin : bdryApprox γ Z k (Icc a b) < ⊤ := by
    unfold bdryApprox
    rw [withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ u in Icc a b, ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
          Real.exp (γ / 2 * avgReg Z k (u : ℂ)))
        ≤ ∫⁻ _ in Icc a b, ENNReal.ofReal C := by
          refine setLIntegral_mono measurable_const fun u hu => ENNReal.ofReal_le_ofReal ?_
          exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC u hu)
      _ = ENNReal.ofReal C * volume (Icc a b) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)
  have hsupp : support h ⊆ Icc a b := fun u hu => by
    by_contra hn; exact hu (hs u hn)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  haveI : IsFiniteMeasure ((bdryApprox γ Z k).restrict (Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨Ch, hCh⟩ := hh.bounded_above_of_compact_support
    (HasCompactSupport.intro isCompact_Icc hs)
  exact Integrable.of_bound hh.aestronglyMeasurable Ch (ae_of_all _ hCh)

/-- A finite net of the dilated test functions. -/
theorem exists_net_dilate {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∀ ε > 0, ∃ S : Finset (ℝ → ℝ),
      (∀ h ∈ S, h ∈ (fun c : ℝ => fun u => f (c * u)) '' Icc 1 2) ∧
      ∀ h ∈ (fun c : ℝ => fun u => f (c * u)) '' Icc 1 2, ∃ h' ∈ S, ∀ x, |h x - h' x| ≤ ε := by
  intro ε hε
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ x, R₀ < |x| → f x = 0 := by
    obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
    refine ⟨max R 0, le_max_right _ _, fun x hx => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
    have := hR h
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_max_left R 0]
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := -(2 * R₀)) (b := 2 * R₀)).uniformContinuousOn_of_continuous
      hf.continuousOn) ε hε
  set δ' : ℝ := δ / (R₀ + 1) with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by linarith [hR₀.1])
  obtain ⟨T, hT, hTf, hcov⟩ := finite_approx_of_totallyBounded
    (isCompact_Icc (a := (1 : ℝ)) (b := 2)).totallyBounded δ' hδ'0
  classical
  refine ⟨hTf.toFinset.image (fun c : ℝ => fun u => f (c * u)), ?_, ?_⟩
  · intro h hh
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hh
    exact ⟨c, hT (hTf.mem_toFinset.1 hc), rfl⟩
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨c', hc'T, hcc'⟩ := mem_iUnion₂.1 (hcov hc)
    refine ⟨fun u => f (c' * u), Finset.mem_image.2 ⟨c', hTf.mem_toFinset.2 hc'T, rfl⟩,
      fun x => ?_⟩
    have hc'I := hT hc'T
    have hd : |c - c'| < δ' := by rw [← Real.dist_eq]; exact mem_ball.1 hcc'
    by_cases hx : |x| ≤ R₀
    · have : dist (c * x) (c' * x) < δ := by
        rw [Real.dist_eq, ← sub_mul, abs_mul]
        calc |c - c'| * |x| ≤ |c - c'| * R₀ := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
          _ ≤ δ' * R₀ := mul_le_mul_of_nonneg_right hd.le hR₀.1
          _ < δ := by
            rw [hδ']
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith [hR₀.1])]
            nlinarith
      have hmem : ∀ d ∈ Icc (1 : ℝ) 2, d * x ∈ Icc (-(2 * R₀)) (2 * R₀) := fun d hd => by
        have h1 : |d * x| ≤ 2 * R₀ := by
          rw [abs_mul, abs_of_pos (by linarith [hd.1] : (0 : ℝ) < d)]
          nlinarith [hd.2, abs_nonneg x]
        exact abs_le.1 h1
      have := hU _ (hmem c hc) _ (hmem c' hc'I) this
      rw [Real.dist_eq] at this
      exact this.le
    · rw [not_le] at hx
      have h1 : f (c * x) = 0 := hR₀.2 _ (by
        rw [abs_mul, abs_of_pos (by linarith [hc.1] : (0 : ℝ) < c)]
        nlinarith [hc.1, abs_nonneg x])
      have h2 : f (c' * x) = 0 := hR₀.2 _ (by
        rw [abs_mul, abs_of_pos (by linarith [hc'I.1] : (0 : ℝ) < c')]
        nlinarith [hc'I.1, abs_nonneg x])
      simp only [h1, h2, sub_zero, abs_zero]
      exact hε.le

end G1Side
end QuantumZipper
