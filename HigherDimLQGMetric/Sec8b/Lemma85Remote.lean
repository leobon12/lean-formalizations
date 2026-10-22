import HigherDimLQGMetric.Sec8b.Lemma85Occupation

/-! A finite perturbation is invisible in a ball remote from its centres. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_F_zero_remote {ξ cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    {r : ℝ} (hr : 0 < r) (Z : Finset (Rd d × ℕ))
    (hJ : ∀ site ∈ Z, site.2 < T.J)
    (z : Rd d)
    (hremote : ∀ site ∈ Z, 10 * r ≤ ‖site.1 - z‖)
    {u : Rd d} (hu : u ∈ ball z (4 * r)) :
    F_Z T.f r Z u = 0 := by
  classical
  simp only [F_Z, ContinuousMap.sum_apply]
  apply Finset.sum_eq_zero
  intro site hsite
  have hnot : u ∉ ball site.1 (4 * r) := by
    intro hu'
    have htri : dist site.1 z ≤ dist site.1 u + dist u z :=
      dist_triangle _ _ _
    have hu1 : dist site.1 u < 4 * r := by
      simpa only [dist_comm] using (mem_ball.mp hu')
    have hu2 : dist u z < 4 * r := by simpa only [dist_comm] using (mem_ball.mp hu)
    have hsep : 10 * r ≤ dist site.1 z := by
      simpa only [dist_eq_norm] using hremote site hsite
    linarith only [htri, hu1, hu2, hsep, hr]
  have hcoll : sec8Collector T.V r site.1 ⊆ ball site.1 (4 * r) := by
    have hcl := S6a.closure_collector_subset hr site.1 T.closureV
    exact subset_closure.trans (hcl.trans (S6a.ann_subset_ball hr site.1))
  have hout : u ∉ sec8Collector T.V r site.1 := fun h => hnot (hcoll h)
  have hf : ∀ v : Rd d, v ∉ T.V → T.f site.2 v = 0 := by
    intro v hv
    have hpos := (T.bumps site.2 (hJ site hsite)).2.2.2.2.1 v
    exact le_antisymm (le_of_not_gt (fun hp => hv (hpos.mp hp)))
      ((T.bumps site.2 (hJ site hsite)).2.2.2.1 v)
  exact S6a.bumpAt_eq_zero_of_notMem hf hr.ne' site.1 hout

theorem s7b_remote_metric_window {ξ cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    {r : ℝ} (hr : 0 < r) (Z : Finset (Rd d × ℕ))
    (hJ : ∀ site ∈ Z, site.2 < T.J)
    (z : Rd d)
    (hremote : ∀ site ∈ Z, 10 * r ≤ ‖site.1 - z‖)
    (Dplus Dbase Dtplus Dtbase : ContMetric d)
    (hDplus : Dplus.IsLength)
    (hW : IsWeylOf ξ (-F_Z T.f r Z) Dplus Dbase)
    (hWt : IsWeylOf ξ (-F_Z T.f r Z) Dtplus Dtbase)
    (P : ℝ → Rd d) {a b : ℝ}
    (hPc : ContinuousOn P (Icc a b))
    (hinside : ∀ t ∈ Icc a b, P t ∈ ball z (4 * r)) :
    Dplus.len P a b = Dbase.len P a b ∧
      ∀ u v : Rd d,
        Dtplus.internal (ball z (4 * r)) u v =
          Dtbase.internal (ball z (4 * r)) u v := by
  have hzero : ∀ u ∈ ball z (4 * r), F_Z T.f r Z u = 0 :=
    fun u hu => s7b_F_zero_remote T hr Z hJ z hremote hu
  have hW0 : IsWeylOf ξ (0 : C(Rd d, ℝ)) Dplus Dplus := by
    intro u v
    simp only [show (0 : C(Rd d, ℝ)) =
        ContinuousMap.const (Rd d) 0 from rfl,
      weylScale_const_of_isLength hDplus, mul_zero, Real.exp_zero,
      one_mul]
  have hlen := s7b_len_eq_of_weyl_weights Dplus Dbase Dplus ξ
    (-F_Z T.f r Z) 0 hW hW0 P hPc (by
      intro t ht
      simp only [ContinuousMap.neg_apply, ContinuousMap.zero_apply,
        hzero (P t) (hinside t ht), neg_zero])
  have hInt : ∀ u v : Rd d,
      Dtbase.internal (ball z (4 * r)) u v =
        Dtplus.internal (ball z (4 * r)) u v := by
    have hf : ∀ u ∈ ball z (4 * r),
        ξ * (-F_Z T.f r Z) u = 0 := by
      intro u hu
      simp only [ContinuousMap.neg_apply, hzero u hu, neg_zero, mul_zero]
    intro u v
    simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using
      (internal_eq_of_eq_const (D' := Dtbase) hWt isOpen_ball hf u v)
  exact ⟨hlen.symm, fun u v => (hInt u v).symm⟩

/-- A nonnegative finite bump sum cannot increase the discounted endpoint
distance. This supplies the missing monotonicity step in the source's
near-extreme inequality for Lemma 8.5. -/
theorem s7b_discount_dist_le {ξ cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt) (hξ : 0 < ξ)
    (r : ℝ) (Z : Finset (Rd d × ℕ))
    (hJ : ∀ site ∈ Z, site.2 < T.J)
    (Dplus Dbase : ContMetric d) (hlen : Dplus.IsLength)
    (hW : IsWeylOf ξ (-F_Z T.f r Z) Dplus Dbase)
    (x y : Rd d) : Dbase.1 (x, y) ≤ Dplus.1 (x, y) := by
  have hF : ∀ u : Rd d, 0 ≤ F_Z T.f r Z u := by
    intro u
    exact (F_Z_nonneg_le
      (fun j hj => ⟨(T.bumps j hj).2.2.2.1,
        (T.bumps j hj).2.2.2.2.2⟩) r hJ u).1
  have hmono : weylScale ξ (-F_Z T.f r Z) Dplus x y ≤
      weylScale ξ (0 : C(Rd d, ℝ)) Dplus x y := by
    apply weylScale_mono_of_le hξ.le
    intro u
    simp only [ContinuousMap.neg_apply, ContinuousMap.zero_apply]
    exact neg_nonpos.mpr (hF u)
  have hreal : ENNReal.ofReal (Dbase.1 (x, y)) ≤
      ENNReal.ofReal (Dplus.1 (x, y)) := by
    calc
      ENNReal.ofReal (Dbase.1 (x, y)) =
          weylScale ξ (-F_Z T.f r Z) Dplus x y := hW x y
      _ ≤ weylScale ξ (0 : C(Rd d, ℝ)) Dplus x y := hmono
      _ = ENNReal.ofReal (Dplus.1 (x, y)) := by
        simp only [show (0 : C(Rd d, ℝ)) =
          ContinuousMap.const (Rd d) 0 from rfl,
          weylScale_const_of_isLength hlen, mul_zero,
          Real.exp_zero, one_mul]
  exact (ENNReal.ofReal_le_ofReal_iff (Dplus.nonneg x y)).mp hreal

end HigherDimLQGMetric
