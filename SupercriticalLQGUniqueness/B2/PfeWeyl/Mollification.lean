import LQGMetric.Papers.DFGPS.L2_12Moll

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


theorem mollCont_fixed_tendsto {ε : ℕ → ℝ} (hε : ∀ n, ε n ≠ 0)
    (hε0 : Tendsto ε atTop (𝓝 0)) (f : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ z, |f z| ≤ M) (R : ℝ) (hR : 0 < R) :
    TendstoUniformlyOn
      (fun n z => LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM z)
      (fun z => f z) atTop (closedBall 0 R) := by
  exact LQGMetric.DFGPS.tendstoUniformlyOn_heatMollify_seq hε hε0
    (fn := fun _ => f) (f := f) (M := M)
    (fun _ z => hM z) hM
    (fun R _ => by
      rw [Metric.tendstoUniformlyOn_iff]
      intro η hη
      exact Filter.Eventually.of_forall (fun n z hz => by simpa using hη)) hR

end SupercriticalLQGUniqueness.B2.PfeWeyl
