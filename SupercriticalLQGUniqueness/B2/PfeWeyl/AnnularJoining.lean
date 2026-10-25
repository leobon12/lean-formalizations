import SupercriticalLQGUniqueness.B2.PfeWeyl.WeylChain
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Transfer.Transfer
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

open Uniqueness.TwoScale.Transfer

 

theorem outside_to_inside_hits_separator
    {Q : ℝ → ℂ} {a b : ℝ} {z : ℂ} {r R : ℝ} {K : Set ℂ}
    (hab : a ≤ b) (hQ : ContinuousOn Q (Icc a b))
    (hrR : r ≤ R)
    (hsep : LQGMetric.Disconnects K (Metric.sphere z r) (Metric.sphere z R))
    (ha : Q a ∉ Metric.ball z R)
    (hb : Q b ∈ Metric.closedBall z r) :
    ∃ q ∈ Icc a b, Q q ∈ K := by
  have hpc : IsPathConnected (Q '' Icc a b) :=
    ((convex_Icc a b).isPathConnected ⟨a, ⟨le_rfl, hab⟩⟩).image' hQ
  have hj : JoinedIn (Q '' Icc a b) (Q a) (Q b) :=
    hpc.joinedIn (Q a) ⟨a, ⟨le_rfl, hab⟩, rfl⟩
      (Q b) ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  obtain ⟨w, ⟨q, rfl⟩, hwK⟩ :=
    ((LQGMetric.Disconnects.closedBall_compl_ball hrR hsep).symm)
      (Q a) (Q b) hj.somePath ha hb
  obtain ⟨q', hq', hQq'⟩ := hj.somePath_mem q
  exact ⟨q', hq', hQq' ▸ hwK⟩

 
theorem inside_to_outside_hits_separator
    {Q : ℝ → ℂ} {a b : ℝ} {z : ℂ} {r R : ℝ} {K : Set ℂ}
    (hab : a ≤ b) (hQ : ContinuousOn Q (Icc a b))
    (hrR : r ≤ R)
    (hsep : LQGMetric.Disconnects K (Metric.sphere z r) (Metric.sphere z R))
    (ha : Q a ∈ Metric.closedBall z r)
    (hb : Q b ∉ Metric.ball z R) :
    ∃ q ∈ Icc a b, Q q ∈ K := by
  have hpc : IsPathConnected (Q '' Icc a b) :=
    ((convex_Icc a b).isPathConnected ⟨a, ⟨le_rfl, hab⟩⟩).image' hQ
  have hj : JoinedIn (Q '' Icc a b) (Q a) (Q b) :=
    hpc.joinedIn (Q a) ⟨a, ⟨le_rfl, hab⟩, rfl⟩
      (Q b) ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  obtain ⟨w, ⟨q, rfl⟩, hwK⟩ :=
    (LQGMetric.Disconnects.closedBall_compl_ball hrR hsep)
      (Q a) (Q b) hj.somePath ha hb
  obtain ⟨q', hq', hQq'⟩ := hj.somePath_mem q
  exact ⟨q', hq', hQq' ▸ hwK⟩

 


theorem annular_join_bound
    (E : LSCMetric) (hforget : Continuous (euclidForget E))
    (A : EuclideanAnnulus)
    {P Q π : ℝ → ℂ} {a b c d s t : ℝ}
    (hP : E.IsCurve P a b) (hQ : E.IsCurve Q c d)
    (_hπ : E.IsCurve π s t)
    (hsep : Disconnects (π '' Icc s t) A.innerBoundary A.outerBoundary)
    (hPa : P a ∉ Metric.ball A.center A.outerRadius)
    (hPb : P b ∈ Metric.closedBall A.center A.innerRadius)
    (hQc0 : Q c ∈ Metric.closedBall A.center A.innerRadius)
    (hQd : Q d ∉ Metric.ball A.center A.outerRadius) :
    E (P a, Q d) ≤ E.len P a b + E.len π s t + E.len Q c d := by
  have hPc : ContinuousOn P (Icc a b) := by
    have hcomp := hforget.continuousOn.comp hP.2 (fun _ _ => Set.mem_univ _)
    convert hcomp using 1
    funext x
    rfl
  have hQcont : ContinuousOn Q (Icc c d) := by
    have hcomp := hforget.continuousOn.comp hQ.2 (fun _ _ => Set.mem_univ _)
    convert hcomp using 1
    funext x
    rfl
  have hsep' : LQGMetric.Disconnects (π '' Icc s t)
      (Metric.sphere A.center A.innerRadius)
      (Metric.sphere A.center A.outerRadius) :=
    Uniqueness.Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  obtain ⟨u, hu, huπ⟩ := outside_to_inside_hits_separator
    hP.1 hPc A.2.2.le hsep' hPa hPb
  obtain ⟨v, hv, hvπ⟩ := inside_to_outside_hits_separator
    hQ.1 hQcont A.2.2.le hsep' hQc0 hQd
  have hPu : E (P a, P u) ≤ E.len P a b :=
    trace_pair_le_len E P ⟨a, ⟨le_rfl, hP.1⟩, rfl⟩ ⟨u, hu, rfl⟩
  have hπuv : E (P u, Q v) ≤ E.len π s t := trace_pair_le_len E π huπ hvπ
  have hQv : E (Q v, Q d) ≤ E.len Q c d :=
    trace_pair_le_len E Q ⟨v, hv, rfl⟩ ⟨d, ⟨hQ.1, le_rfl⟩, rfl⟩
  calc
    E (P a, Q d) ≤ E (P a, P u) + E (P u, Q v) + E (Q v, Q d) := by
      calc
        _ ≤ E (P a, P u) + E (P u, Q d) := E.isExtMetric.2.2.2 _ _ _
        _ ≤ E (P a, P u) + (E (P u, Q v) + E (Q v, Q d)) := by
          gcongr
          exact E.isExtMetric.2.2.2 _ _ _
        _ = _ := by ac_rfl
    _ ≤ E.len P a b + E.len π s t + E.len Q c d := by
      exact add_le_add (add_le_add hPu hπuv) hQv

 


theorem aroundDist_exists_curve_lt (E : LSCMetric) (A : EuclideanAnnulus)
    {δ : ℝ} (hδ : aroundDist E A < ENNReal.ofReal δ) :
    ∃ (π : ℝ → ℂ) (s t : ℝ), E.IsCurve π s t ∧
      (∀ u ∈ Icc s t, π u ∈ A.toSet) ∧
      Disconnects (π '' Icc s t) A.innerBoundary A.outerBoundary ∧
      E.len π s t < ENNReal.ofReal δ := by
  unfold aroundDist at hδ
  simp only [iInf_lt_iff] at hδ
  obtain ⟨π, s, t, hπ, hA, hsep, hlen⟩ := hδ
  exact ⟨π, s, t, hπ, hA, hsep, hlen⟩

theorem annular_join_of_around_lt
    (E : LSCMetric) (hforget : Continuous (euclidForget E))
    (A : EuclideanAnnulus)
    {P Q : ℝ → ℂ} {a b c d δ : ℝ}
    (hP : E.IsCurve P a b) (hQ : E.IsCurve Q c d)
    (hPa : P a ∉ Metric.ball A.center A.outerRadius)
    (hPb : P b ∈ Metric.closedBall A.center A.innerRadius)
    (hQc : Q c ∈ Metric.closedBall A.center A.innerRadius)
    (hQd : Q d ∉ Metric.ball A.center A.outerRadius)
    (hδ : aroundDist E A < ENNReal.ofReal δ) :
    E (P a, Q d) ≤ E.len P a b + ENNReal.ofReal δ + E.len Q c d := by
  obtain ⟨π, s, t, hπ, _, hsep, hlen⟩ := aroundDist_exists_curve_lt E A hδ
  exact (annular_join_bound E hforget A hP hQ hπ hsep hPa hPb hQc hQd).trans
    (add_le_add (add_le_add le_rfl hlen.le) le_rfl)

end SupercriticalLQGUniqueness.B2.PfeWeyl
