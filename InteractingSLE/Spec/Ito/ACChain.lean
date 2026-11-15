import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The chain rule for absolutely continuous paths

Packet PROVE-T11-ITO. The coordinates of the integrated `SLE_κ(ρ)` evolution (Definition 2.1) are
absolutely continuous in time with only *integrable* densities (the reciprocal gaps
`1/(W − V^{i,q})`); the time-integrals of the Itô expansions are therefore chain rules for absolutely
continuous paths, not for `C¹` paths. This file proves the chain rule needed:

* `absolutelyContinuousOnInterval_of_dist_le`: a path dominated (in distance) by an absolutely
  continuous path is absolutely continuous;
* `absolutelyContinuousOnInterval_intervalIntegral'`: `x ↦ ∫_c^x λ` is absolutely continuous for an
  integrable `λ` with values in any Banach space (Mathlib has the real-valued case);
* `comp_eq_add_integral_of_lipschitz`: if `Λ t = Λ a + ∫_a^t λ` on `[a, b]` with `λ` integrable and
  `Φ : E → ℝ` is Lipschitz with continuous derivative `Φ'`, then
  `Φ (Λ b) = Φ (Λ a) + ∫_a^b Φ'(Λ s) (λ s) ds`.

The proof is Lebesgue's differentiation theorem (`IntervalIntegrable.ae_hasDerivAt_integral`) and the
vanishing-derivative theorem for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal

namespace InteractingSLE

namespace Ito

/-- A path whose increments are dominated by those of an absolutely continuous path is absolutely
continuous. -/
theorem absolutelyContinuousOnInterval_of_dist_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  unfold AbsolutelyContinuousOnInterval at hg ⊢
  refine squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
    ?_ hg
  rw [eventually_inf_principal]
  exact Eventually.of_forall fun E hE =>
    Finset.sum_le_sum fun i hi => h _ (hE.1 i hi).1 _ (hE.1 i hi).2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- `x ↦ ∫_c^x λ` is absolutely continuous on `[a, b]` for `λ` integrable on `[a, b]` with values in a
Banach space. -/
theorem absolutelyContinuousOnInterval_intervalIntegral' {lam : ℝ → E} {a b c : ℝ}
    (h : IntervalIntegrable lam volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, lam v) a b := by
  refine absolutelyContinuousOnInterval_of_dist_le
    (h.norm.absolutelyContinuousOnInterval_intervalIntegral hc) fun x hx y hy => ?_
  have hxy : IntervalIntegrable lam volume x y := h.mono_set (uIcc_subset_uIcc hx hy)
  have hcx : IntervalIntegrable lam volume c x := h.mono_set (uIcc_subset_uIcc hc hx)
  have hcy : IntervalIntegrable lam volume c y := h.mono_set (uIcc_subset_uIcc hc hy)
  rw [dist_eq_norm, dist_eq_norm, intervalIntegral.integral_interval_sub_left hcx hcy,
    intervalIntegral.integral_interval_sub_left hcx.norm hcy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm.trans_eq (Real.norm_eq_abs _).symm

/-- **Chain rule for absolutely continuous paths.** Let `Λ t = Λ a + ∫_a^t λ` on `[a, b]`, `λ`
integrable, and let `Φ : E → ℝ` be Lipschitz with continuous derivative `Φ'`. Then
`Φ (Λ b) = Φ (Λ a) + ∫_a^b Φ'(Λ s) (λ s) ds`. -/
theorem comp_eq_add_integral_of_lipschitz {Φ : E → ℝ} {Φ' : E → E →L[ℝ] ℝ} {K : ℝ≥0}
    (hΦ : ∀ x, HasFDerivAt Φ (Φ' x) x) (hΦL : LipschitzWith K Φ) (hΦ' : Continuous Φ')
    {Λ lam : ℝ → E} {a b : ℝ} (hlam : IntervalIntegrable lam volume a b)
    (hΛ : ∀ t ∈ uIcc a b, Λ t = Λ a + ∫ s in a..t, lam s) :
    Φ (Λ b) = Φ (Λ a) + ∫ s in a..b, Φ' (Λ s) (lam s) := by
  have ha : a ∈ uIcc a b := left_mem_uIcc
  -- the path is absolutely continuous, hence continuous
  have hAC : AbsolutelyContinuousOnInterval Λ a b := by
    have h1 := absolutelyContinuousOnInterval_intervalIntegral' hlam ha
    have h2 : AbsolutelyContinuousOnInterval (fun t => Λ a + ∫ s in a..t, lam s) a b := by
      refine absolutelyContinuousOnInterval_of_dist_le h1 fun x _ y _ => ?_
      rw [dist_add_left]
    exact h2.congr fun t ht => (hΛ t ht).symm
  have hΛc : ContinuousOn Λ (uIcc a b) := hAC.continuousOn
  -- the integrand is integrable
  have hg : IntervalIntegrable (fun s => Φ' (Λ s) (lam s)) volume a b := by
    have hbd : ∀ x, ‖Φ' x‖ ≤ K := fun x => by
      have := norm_fderiv_le_of_lipschitz ℝ hΦL (x₀ := x)
      rwa [(hΦ x).fderiv] at this
    refine (hlam.norm.const_mul (K : ℝ)).mono_fun' ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun s => Φ' (Λ s)) (volume.restrict (uIoc a b)) :=
        ((hΦ'.comp_continuousOn hΛc).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
      have hm2 : AEStronglyMeasurable lam (volume.restrict (uIoc a b)) :=
        (intervalIntegrable_iff.1 hlam).aestronglyMeasurable
      exact (continuous_fst.clm_apply continuous_snd :
        Continuous fun p : (E →L[ℝ] ℝ) × E => p.1 p.2).comp_aestronglyMeasurable₂ hm1 hm2
    · exact Eventually.of_forall fun s => ((Φ' (Λ s)).le_opNorm (lam s)).trans
        (mul_le_mul_of_nonneg_right (hbd _) (norm_nonneg _))
  -- the defect `ψ` is absolutely continuous with derivative zero almost everywhere
  set ψ : ℝ → ℝ := fun t => Φ (Λ t) - ∫ s in a..t, Φ' (Λ s) (lam s) with hψ
  have hψAC : AbsolutelyContinuousOnInterval ψ a b :=
    (hΦL.comp_absolutelyContinuousOnInterval hAC).sub
      (hg.absolutelyContinuousOnInterval_intervalIntegral ha)
  have hder : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt ψ 0 x := by
    have hΛd := hlam.ae_hasDerivAt_integral
    have hgd := hg.ae_hasDerivAt_integral
    have hend : ∀ᵐ x : ℝ, x ≠ a ∧ x ≠ b := by
      have h1 : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
      have h2 : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
      filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩
    filter_upwards [hΛd, hgd, hend] with x hx1 hx2 hx3 hx
    have hxo : x ∈ Ioo (min a b) (max a b) := by
      rw [uIcc, mem_Icc] at hx
      refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
      · intro h; rcases min_choice a b with h' | h' <;> rw [h'] at h
        · exact hx3.1 h.symm
        · exact hx3.2 h.symm
      · intro h; rcases max_choice a b with h' | h' <;> rw [h'] at h
        · exact hx3.1 h
        · exact hx3.2 h
    have hnhds : uIcc a b ∈ 𝓝 x := by
      rw [uIcc]; exact Icc_mem_nhds hxo.1 hxo.2
    have hΛx : HasDerivAt Λ (lam x) x := by
      refine ((hx1 hx a ha).const_add (Λ a)).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with t ht using hΛ t ht
    have h1 : HasDerivAt (fun t => Φ (Λ t)) (Φ' (Λ x) (lam x)) x :=
      (hΦ (Λ x)).comp_hasDerivAt x hΛx
    have h2 := hx2 hx a ha
    exact (h1.fun_sub h2).congr_deriv (sub_self _)
  obtain ⟨C, hC⟩ := hψAC.const_of_ae_hasDerivAt_zero hder
  have hb := hC b right_mem_uIcc
  have ha' := hC a ha
  simp only [hψ, intervalIntegral.integral_same, sub_zero] at hb ha'
  linarith

end Ito

end InteractingSLE
