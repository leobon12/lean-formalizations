import QuantumZipper.Proofs.Zipper.SWCoreN2Fam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (4): admissibility of pushed semicircles of a boundary class

For a boundary class `BdryClass a b ρ M m` (`a < b`, `ρ, m > 0`) there is `r₀ > 0` such that for
all `ψ` of the class, `t ∈ [a,b]` and `r ∈ (0, r₀)`, the pushed semicircle `fc(t,r).map ψ` is an
admissible probability measure (`swcn2_push_admissible`): it is the image of `fc(t,r)` (carried by
`B̄(t,r) ∩ ℍ̄`) under a map that is continuous, `(ψ'(t)/2)`-co-Lipschitz and preserves `Im ≥ 0`
there (`swcv_ball_facts`), so `isAdmissibleH_map` applies. Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif

/-- `fc(t,r)` is carried by `B̄(t,r) ∩ ℍ̄`. -/
theorem swcn2_fc_supp (t : ℝ) {r : ℝ} (hr : 0 < r) :
    foldedCircle (t : ℂ) r (closedBall (t : ℂ) r ∩ Hbar)ᶜ = 0 := by
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  have haeB : ∀ᵐ u ∂μ₀, ‖u‖ = 1 := swcv_ae_norm_fc01
  have haeH : ∀ᵐ u ∂μ₀, u ∈ Hbar := by
    have hHm : MeasurableSet {x : ℂ | x ∈ Hbar} :=
      measurableSet_le measurable_const Complex.measurable_im
    rw [hμ₀, foldedCircle, ae_map_iff measurable_foldH.aemeasurable hHm]
    exact Eventually.of_forall fun w => CircleFubini.foldH_mem_Hbar' w
  have hS : MeasurableSet {x : ℂ | x ∈ closedBall (t : ℂ) r ∩ Hbar} :=
    measurableSet_closedBall.inter (measurableSet_le measurable_const Complex.measurable_im)
  have h : ∀ᵐ x ∂foldedCircle (t : ℂ) r, x ∈ closedBall (t : ℂ) r ∩ Hbar := by
    rw [swcv_fc_eq_map t hr, ae_map_iff (measurable_swhAff t r).aemeasurable hS]
    filter_upwards [haeB, haeH] with u hu huH
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      unfold swhAff
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hu,
        mul_one]
    · unfold swhAff
      have : (0 : ℝ) ≤ u.im := huH
      show 0 ≤ ((t : ℂ) + (r : ℂ) * u).im
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
        zero_mul, add_zero]
      exact mul_nonneg hr.le this
  exact ae_iff.1 h

/-- **Pushed semicircles of a class are admissible probability measures.** -/
theorem swcn2_push_admissible (a b ρ M m : ℝ) (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ψ ∈ BdryClass a b ρ M m, ∀ t ∈ Icc a b, ∀ r ∈ Ioo 0 r₀,
      IsAdmissibleH ((foldedCircle (t : ℂ) r).map ψ) ∧
        ((foldedCircle (t : ℂ) r).map ψ) univ = 1 := by
  classical
  obtain ⟨r₁, hr₁, C, hC, hF⟩ := swcv_ball_facts a b ρ M m hab hρ hm
  refine ⟨min r₁ (ρ / 2), lt_min hr₁ (by linarith), fun ψ hψ t ht r hr => ?_⟩
  have hrr₁ : r < r₁ := lt_of_lt_of_le hr.2 (min_le_left _ _)
  have hrρ : r < ρ / 2 := lt_of_lt_of_le hr.2 (min_le_right _ _)
  obtain ⟨⟨hmD, -⟩, hL, hI⟩ := hF ψ hψ t ht r ⟨hr.1, hrr₁⟩
  have hD : 0 < (deriv ψ t).re := lt_of_lt_of_le hm hmD
  have hball : closedBall (t : ℂ) r ⊆ thickening ρ (segC a b) := fun z hz => by
    rw [mem_thickening_iff]
    refine ⟨(t : ℂ), ⟨t, ht, rfl⟩, ?_⟩
    have := mem_closedBall.1 hz
    linarith
  have hψc : ContinuousOn ψ (closedBall (t : ℂ) r) := (hψ.1.mono hball).continuousOn
  set ψm : ℂ → ℂ := (closedBall (t : ℂ) r).piecewise ψ id with hψm
  have hψmm : Measurable ψm :=
    ContinuousOn.measurable_piecewise hψc continuous_id.continuousOn measurableSet_closedBall
  have hsupp := swcn2_fc_supp t hr.1
  have heq : (foldedCircle (t : ℂ) r).map ψ = (foldedCircle (t : ℂ) r).map ψm := by
    have hsub : {x : ℂ | ¬ ψ x = ψm x} ⊆ (closedBall (t : ℂ) r ∩ Hbar)ᶜ := fun x hx hxc => by
      apply hx
      rw [hψm, piecewise_eq_of_mem _ _ _ hxc.1]
    exact Measure.map_congr (ae_iff.2 (measure_mono_null hsub hsupp))
  rw [heq]
  have hadm0 : IsAdmissibleH (foldedCircle (t : ℂ) r) :=
    D3Plus.isAdmissibleH_foldedCircle' _ hr.1
  have hK : IsCompact (closedBall (t : ℂ) r ∩ Hbar) := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  refine ⟨isAdmissibleH_map hadm0 hK hsupp hψmm
    ((hψc.congr fun z hz => by rw [hψm, piecewise_eq_of_mem _ _ _ hz]).mono inter_subset_left)
    ?_ (half_pos hD) fun x hx y hy => ?_, ?_⟩
  · rintro _ ⟨z, ⟨hz, hzH⟩, rfl⟩
    show 0 ≤ (ψm z).im
    rw [hψm, piecewise_eq_of_mem _ _ _ hz]
    exact hI z hz hzH
  · rw [hψm, piecewise_eq_of_mem _ _ _ hx.1, piecewise_eq_of_mem _ _ _ hy.1]
    exact (hL x hx.1 y hy.1).1
  · rw [Measure.map_apply hψmm MeasurableSet.univ, preimage_univ, measure_univ]

end SWCore
end QuantumZipper
