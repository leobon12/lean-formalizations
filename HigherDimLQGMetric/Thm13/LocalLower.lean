import HigherDimLQGMetric.Thm13.ConfinedLower
import HigherDimLQGMetric.Locality.Exhaust

/-! Confined lower semicontinuity for relatively compact open domains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

theorem l8_internal_liminf_ge_enlarged_domain
    {d : ℕ} (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hD : D.IsLength)
    (hconv : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    (W U : TopologicalSpace.Opens (Rd d))
    (hWc : IsPreconnected (W : Set (Rd d)))
    (hK : IsCompact (closure (W : Set (Rd d))))
    (hKU : closure (W : Set (Rd d)) ⊆ U)
    (u v : Rd d) (hu : u ∈ W) (hv : v ∈ W) :
    D.internal U u v ≤
      liminf (fun n => (Dn n).internal W u v) atTop := by
  let K : Set (Rd d) := closure (W : Set (Rd d))
  have hKfin : D.internal K u v ≠ ∞ := by
    have hfin := D.internal_ne_top_of_isPreconnected
      hD W.isOpen hWc hu hv
    exact ne_top_of_le_ne_top hfin
      (D.internal_anti subset_closure u v)
  have hρ (n : ℕ) : IsCoordinate (fun p : Rd d × Rd d => (Dn n).1 p) := by
    exact ⟨⟨(Dn n).2.self_eq_zero, (Dn n).2.eq_of_eq_zero,
      (Dn n).2.symm, (Dn n).2.triangle⟩,
      (Dn n).continuous_pt, (Dn n).continuous_unpt⟩
  have huni : TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop (K ×ˢ K) :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv) _
      (hK.prod hK)
  have hmod : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      ∀ n, ∀ x ∈ K, ∀ y ∈ K, (Dn n).1 (x,y) < b → dist x y < χ :=
    fun χ hχ => l8_common_inverse_modulus Dn D hconv hK hχ
  have hWfin : weylDistOnWith
      (fun x y => ENNReal.ofReal (D.1 (x,y))) (fun _ => 1) K u v ≠ ∞ := by
    rw [l8_weylDistOnWith_one]
    exact hKfin
  have hbound (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop,
        D.internal U u v ≤
          (Dn n).internal W u v + ENNReal.ofReal ε := by
    have hevent := lemma25_moving_lower hK
      (fun n p => (Dn n).1 p) D.1 hρ huni hmod
      (fun _ => 1) continuous_const.continuousOn (fun _ _ => one_pos)
      (fun _ => u) (fun _ => v) u v tendsto_const_nhds tendsto_const_nhds
      hWfin hε
    filter_upwards [hevent] with n hn
    calc
      D.internal U u v ≤ D.internal K u v := D.internal_anti hKU u v
      _ = weylDistOnWith (fun x y => ENNReal.ofReal (D.1 (x,y)))
          (fun _ => 1) K u v := (l8_weylDistOnWith_one D K u v).symm
      _ ≤ weylDistOnWith (fun x y => ENNReal.ofReal ((Dn n).1 (x,y)))
          (fun _ => 1) K u v + ENNReal.ofReal ε := hn
      _ = (Dn n).internal K u v + ENNReal.ofReal ε := by
        rw [l8_weylDistOnWith_one]
      _ ≤ (Dn n).internal W u v + ENNReal.ofReal ε :=
        add_le_add ((Dn n).internal_anti subset_closure u v) le_rfl
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hlim : D.internal U u v ≤
      liminf (fun n => (Dn n).internal W u v + ENNReal.ofReal (ε : ℝ)) atTop :=
    Filter.le_liminf_of_le (hf := by isBoundedDefault) (hbound ε hε)
  rw [liminf_add_const atTop (fun n => (Dn n).internal W u v)
    (ENNReal.ofReal (ε : ℝ)) (by isBoundedDefault) (by isBoundedDefault)] at hlim
  simpa only [ENNReal.ofReal_coe_nnreal] using hlim

end HigherDimLQGMetric
