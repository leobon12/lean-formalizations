import SupercriticalLQGUniqueness.B2.PfeWeyl.WeylChain
import LQGMetric.Topo.RectCross
import SLUMetricAPI2

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem continuousOn_of_isCurve_of_forget (E : LSCMetric)
    (hforget : Continuous (euclidForget E)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : E.IsCurve P a b) : ContinuousOn P (Icc a b) :=
  hforget.comp_continuousOn hP.2

 
theorem len_mono_Icc (E : LSCMetric) (P : ℝ → ℂ) {a b s t : ℝ}
    (has : a ≤ s) (htb : t ≤ b) : E.len P s t ≤ E.len P a b :=
  eVariationOn.mono (E.pt ∘ P) (Icc_subset_Icc has htb)

 


theorem acrossDist_le_len_of_crossing (E : LSCMetric) (A : EuclideanAnnulus)
    {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hPc : ContinuousOn P (Icc a b))
    (ha : dist (P a) A.center ≤ A.innerRadius)
    (hb : A.outerRadius ≤ dist (P b) A.center) :
    acrossDist E A ≤ E.len P a b := by
  have hf : ContinuousOn (fun u => dist (P u) A.center) (Icc a b) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  obtain ⟨s, t, has, hst, htb, hs, ht, _⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hab hf
      A.innerRadius_lt_outerRadius.le ha hb
  have hcross : acrossDist E A ≤ E (P s, P t) := by
    unfold acrossDist
    exact iInf_le_of_le (P s) (iInf_le_of_le
      (by simpa only [EuclideanAnnulus.innerBoundary, Metric.mem_sphere] using hs)
      (iInf_le_of_le (P t) (iInf_le_of_le
        (by simpa only [EuclideanAnnulus.outerBoundary, Metric.mem_sphere] using ht)
        le_rfl)))
  exact hcross.trans ((LSCMetric.apply_le_len E P hst).trans
    (len_mono_Icc E P has htb))

 


theorem curve_mem_ball_of_len_lt_acrossDist (E : LSCMetric) (A : EuclideanAnnulus)
    {P : ℝ → ℂ} {a b : ℝ} (hPc : ContinuousOn P (Icc a b))
    (ha : dist (P a) A.center ≤ A.innerRadius)
    (hlen : E.len P a b < acrossDist E A) :
    ∀ t ∈ Icc a b, P t ∈ Metric.ball A.center A.outerRadius := by
  intro t ht
  by_contra hout
  have hfar : A.outerRadius ≤ dist (P t) A.center := by
    simpa only [Metric.mem_ball, not_lt] using hout
  have hcross := acrossDist_le_len_of_crossing E A ht.1
    (hPc.mono (Icc_subset_Icc le_rfl ht.2)) ha hfar
  exact (not_lt_of_ge (hcross.trans (len_mono_Icc E P le_rfl ht.2))) hlen

end SupercriticalLQGUniqueness.B2.PfeWeyl
