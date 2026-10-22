import HigherDimLQGMetric.Thm13.LocalFormula
import HigherDimLQGMetric.Limits.JointInternalDet

/-! Upper bound for internal lower limits from L6c's joint limit consistency. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

theorem l8_internal_liminf_le_internal
    {d : ℕ} (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    (W : TopologicalSpace.Opens (Rd d))
    (hWc : IsPreconnected (W : Set (Rd d)))
    (u v : Rd d) (hu : u ∈ W) (hv : v ∈ W) :
    liminf (fun n => (Dn n).internal W u v) atTop ≤
      D.internal W u v := by
  obtain ⟨E, φ, hφ, hEconv, hE, _, _, hEintr⟩ :=
    l6c_internal_subseq_consistent Dn D hDn hconv W.isOpen hWc
  let a : W := ⟨u, hu⟩
  let b : W := ⟨v, hv⟩
  have hpt : Tendsto
      (fun n => ((Dn (φ n)).internal W u v).toReal)
      atTop (𝓝 (E (a,b))) := by
    exact (continuous_eval_const (a,b)).continuousAt.tendsto.comp hEconv
  have hfin (n : ℕ) : (Dn (φ n)).internal W u v ≠ ∞ :=
    (Dn (φ n)).internal_ne_top_of_isPreconnected
      (hDn (φ n)) W.isOpen hWc hu hv
  have hpt' : Tendsto
      (fun n => (Dn (φ n)).internal W u v)
      atTop (𝓝 (ENNReal.ofReal (E (a,b)))) := by
    have ht := (ENNReal.continuous_ofReal.tendsto _).comp hpt
    convert ht using 1
    funext n
    exact (ENNReal.ofReal_toReal (hfin n)).symm
  have hlim : liminf (fun n => (Dn n).internal W u v) atTop ≤
      ENNReal.ofReal (E (a,b)) := by
    calc
      liminf (fun n => (Dn n).internal W u v) atTop ≤
          liminf (fun n => (Dn (φ n)).internal W u v) atTop :=
        Filter.Tendsto.liminf_le_liminf_comp hφ.tendsto_atTop
      _ = ENNReal.ofReal (E (a,b)) := hpt'.liminf_eq
  have hmetric : ENNReal.ofReal (E (a,b)) ≤ D.internal W u v := by
    rw [hEintr a b]
    simpa only [edist_dist, MetricFunSpace.dist_pt] using
      (edist_le_internalEDist Set.univ
        (MetricFunSpace.pt E hE a) (MetricFunSpace.pt E hE b))
  exact hlim.trans hmetric

end HigherDimLQGMetric
