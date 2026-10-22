import HigherDimLQGMetric.Locality.TwoTruncCoupling
import HigherDimLQGMetric.Locality.BoundSeq

/-! Bounds for the scalar normalization and a compactly supported Markov
cutoff on a moving-field coupling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_marked_perturb_bounds {d : ℕ}
    {E : Type*} [MeasurableSpace E] (Q : Measure E)
    (cn : ℕ → E → ℝ) (c : E → ℝ)
    (Fn : ℕ → E → C(Rd d, ℝ)) (F : E → C(Rd d, ℝ))
    (hcn : ∀ᵐ e ∂Q, Tendsto (fun n => cn n e) atTop (𝓝 (c e)))
    (hFn : ∀ᵐ e ∂Q, Tendsto (fun n => Fn n e) atTop (𝓝 (F e)))
    (K : Set (Rd d)) (hK : IsCompact K)
    (hsupp : ∀ᵐ e ∂Q, ∀ n z, z ∉ K → Fn n e z = 0) :
    let fn₁ : ℕ → E → C(Rd d, ℝ) := fun n e =>
      ContinuousMap.const (Rd d) (-cn n e)
    let fn₂ : ℕ → E → C(Rd d, ℝ) := fun n e =>
      ContinuousMap.const (Rd d) (-cn n e) - Fn n e
    let f₁ : E → C(Rd d, ℝ) := fun e =>
      ContinuousMap.const (Rd d) (-c e)
    let f₂ : E → C(Rd d, ℝ) := fun e =>
      ContinuousMap.const (Rd d) (-c e) - F e
    (∀ᵐ e ∂Q, ∃ M : ℝ, ∀ n z, |fn₁ n e z| ≤ M) ∧
    (∀ᵐ e ∂Q, ∃ M : ℝ, ∀ n z, |fn₂ n e z| ≤ M) ∧
    (∀ᵐ e ∂Q, Tendsto (fun n => fn₁ n e) atTop (𝓝 (f₁ e))) ∧
    (∀ᵐ e ∂Q, Tendsto (fun n => fn₂ n e) atTop (𝓝 (f₂ e))) := by
  dsimp only
  have hneg : Continuous (fun a : ℝ => -a) := continuous_neg
  have hconst : Continuous (fun a : ℝ => ContinuousMap.const (Rd d) a) := by
    fun_prop
  have hminus : Continuous (fun q : ℝ × C(Rd d, ℝ) =>
      ContinuousMap.const (Rd d) (-q.1) - q.2) := by
    fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hcn] with e he
    obtain ⟨M, hM⟩ := (hneg.tendsto (c e)).comp he |>.isCompact_insert_range.exists_bound_of_continuousOn
      (continuous_id : Continuous (fun x : ℝ => x)).continuousOn
    exact ⟨M, fun n z => by
      simpa only [ContinuousMap.const_apply, Real.norm_eq_abs, id_eq] using
        hM (-cn n e) (mem_insert_of_mem _ (mem_range_self n))⟩
  · filter_upwards [hcn, hFn, hsupp] with e hc hf hs
    have hcn' : Tendsto (fun n => -cn n e) atTop (𝓝 (-c e)) :=
      (hneg.tendsto (c e)).comp hc
    have hFn' : Tendsto (fun n => -Fn n e) atTop (𝓝 (-F e)) :=
      (continuous_neg.tendsto (F e)).comp hf
    obtain ⟨M, hM⟩ := l7a_exists_bound_const_add_supp hcn' hFn' hK
      (fun n z hz => by simp only [ContinuousMap.neg_apply, hs n z hz, neg_zero])
    exact ⟨M, fun n z => by
      simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply,
        ContinuousMap.neg_apply, sub_eq_add_neg] using hM n z⟩
  · filter_upwards [hcn] with e he
    exact (hconst.tendsto (-c e)).comp ((hneg.tendsto (c e)).comp he)
  · filter_upwards [hcn, hFn] with e hc hf
    have hp : Tendsto (fun n => (cn n e, Fn n e)) atTop
        (𝓝 (c e, F e)) := by
      simpa only [nhds_prod_eq] using hc.prodMk hf
    exact (hminus.tendsto (c e, F e)).comp hp

end HigherDimLQGMetric
