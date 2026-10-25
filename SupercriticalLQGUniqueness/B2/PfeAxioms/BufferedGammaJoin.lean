import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaPairs
import SupercriticalLQGUniqueness.B2.PfeWeyl.AnnularJoining

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem internal_trace_pair_le_len
    (E : LSCMetric) {V : Set ℂ} {P : ℝ → ℂ} {a b s t : ℝ}
    (hP : E.IsCurve P a b)
    (hV : ∀ u ∈ Icc a b, P u ∈ V)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    E.internal V (⟨P s, hV s hs⟩, ⟨P t, hV t ht⟩) ≤ E.len P a b := by
  have hstep : ∀ {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b)
      (huv : u ≤ v),
      E.internal V (⟨P u, hV u hu⟩, ⟨P v, hV v hv⟩) ≤ E.len P a b := by
    intro u v hu hv huv
    rw [LSCMetric.internal_eq_internalEDist]
    have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    have hcost := LQGMetric.MetricGeometry.internalEDist_le_curveLength
      (X := E.Space) (Y := E.pt '' V) (P := E.pt ∘ P) huv
      (hP.2.mono hsub) (fun w hw => ⟨P w, hV w (hsub hw), rfl⟩)
    exact hcost.trans
      (LQGMetric.MetricGeometry.curveLength_mono (E.pt ∘ P) hu.1 hv.2)
  rcases le_total s t with hst | hts
  · exact hstep hs ht hst
  · have h := hstep ht hs hts
    simpa only [(E.isExtMetric_internal V).2.2.1] using h

theorem internal_trace_pair_le_len_of_mem
    (E : LSCMetric) {V : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : E.IsCurve P a b)
    (hV : ∀ u ∈ Icc a b, P u ∈ V)
    {x y : ℂ} (hx : x ∈ P '' Icc a b) (hy : y ∈ P '' Icc a b)
    (hxV : x ∈ V) (hyV : y ∈ V) :
    E.internal V (⟨x, hxV⟩, ⟨y, hyV⟩) ≤ E.len P a b := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  exact internal_trace_pair_le_len E hP hV hs ht

 

theorem buffered_annular_join_bound
    (E : LSCMetric) (hforget : Continuous (euclidForget E))
    {V : Set ℂ} (A : EuclideanAnnulus)
    {P Q π : ℝ → ℂ} {a b c d s t : ℝ}
    (hP : E.IsCurve P a b) (hQ : E.IsCurve Q c d)
    (hπ : E.IsCurve π s t)
    (hPV : ∀ u ∈ Icc a b, P u ∈ V)
    (hQV : ∀ u ∈ Icc c d, Q u ∈ V)
    (hπV : ∀ u ∈ Icc s t, π u ∈ V)
    (hsep : Disconnects (π '' Icc s t) A.innerBoundary A.outerBoundary)
    (hPa : P a ∉ Metric.ball A.center A.outerRadius)
    (hPb : P b ∈ Metric.closedBall A.center A.innerRadius)
    (hQc : Q c ∈ Metric.closedBall A.center A.innerRadius)
    (hQd : Q d ∉ Metric.ball A.center A.outerRadius) :
    E.internal V
      (⟨P a, hPV a ⟨le_rfl, hP.1⟩⟩,
        ⟨Q d, hQV d ⟨hQ.1, le_rfl⟩⟩) ≤
      E.len P a b + E.len π s t + E.len Q c d := by
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
  obtain ⟨u, hu, huπ⟩ := PfeWeyl.outside_to_inside_hits_separator
    hP.1 hPc A.2.2.le hsep' hPa hPb
  obtain ⟨v, hv, hvπ⟩ := PfeWeyl.inside_to_outside_hits_separator
    hQ.1 hQcont A.2.2.le hsep' hQc hQd
  let pa : V := ⟨P a, hPV a ⟨le_rfl, hP.1⟩⟩
  let pu : V := ⟨P u, hPV u hu⟩
  let qv : V := ⟨Q v, hQV v hv⟩
  let qd : V := ⟨Q d, hQV d ⟨hQ.1, le_rfl⟩⟩
  have hPu : E.internal V (pa, pu) ≤ E.len P a b :=
    internal_trace_pair_le_len E hP hPV ⟨le_rfl, hP.1⟩ hu
  have hπuv : E.internal V (pu, qv) ≤ E.len π s t :=
    internal_trace_pair_le_len_of_mem E hπ hπV huπ hvπ (hPV u hu) (hQV v hv)
  have hQv : E.internal V (qv, qd) ≤ E.len Q c d :=
    internal_trace_pair_le_len E hQ hQV hv ⟨hQ.1, le_rfl⟩
  have hE := E.isExtMetric_internal V
  calc
    E.internal V (pa, qd) ≤
        E.internal V (pa, pu) + E.internal V (pu, qv) +
          E.internal V (qv, qd) := by
      calc
        _ ≤ E.internal V (pa, pu) + E.internal V (pu, qd) := hE.2.2.2 _ _ _
        _ ≤ E.internal V (pa, pu) +
            (E.internal V (pu, qv) + E.internal V (qv, qd)) := by
          gcongr
          exact hE.2.2.2 _ _ _
        _ = _ := by ac_rfl
    _ ≤ E.len P a b + E.len π s t + E.len Q c d := by
      exact add_le_add (add_le_add hPu hπuv) hQv

theorem buffered_annular_join_of_around_lt
    (E : LSCMetric) (hforget : Continuous (euclidForget E))
    {V : Set ℂ} (A : EuclideanAnnulus) (hAV : A.toSet ⊆ V)
    {P Q : ℝ → ℂ} {a b c d δ : ℝ}
    (hP : E.IsCurve P a b) (hQ : E.IsCurve Q c d)
    (hPV : ∀ u ∈ Icc a b, P u ∈ V)
    (hQV : ∀ u ∈ Icc c d, Q u ∈ V)
    (hPa : P a ∉ Metric.ball A.center A.outerRadius)
    (hPb : P b ∈ Metric.closedBall A.center A.innerRadius)
    (hQc : Q c ∈ Metric.closedBall A.center A.innerRadius)
    (hQd : Q d ∉ Metric.ball A.center A.outerRadius)
    (hδ : aroundDist E A < ENNReal.ofReal δ) :
    E.internal V
      (⟨P a, hPV a ⟨le_rfl, hP.1⟩⟩,
        ⟨Q d, hQV d ⟨hQ.1, le_rfl⟩⟩) ≤
      E.len P a b + ENNReal.ofReal δ + E.len Q c d := by
  obtain ⟨π, s, t, hπ, hπA, hsep, hlen⟩ :=
    PfeWeyl.aroundDist_exists_curve_lt E A hδ
  exact (buffered_annular_join_bound E hforget A hP hQ hπ hPV hQV
      (fun u hu => hAV (hπA u hu)) hsep hPa hPb hQc hQd).trans
    (add_le_add (add_le_add le_rfl hlen.le) le_rfl)

end SupercriticalLQGUniqueness.B2.PfeAxioms
